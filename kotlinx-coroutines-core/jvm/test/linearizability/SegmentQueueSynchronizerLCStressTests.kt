/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")
package kotlinx.coroutines.linearizability

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.check
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer.CancellationMode.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer.ResumeMode.*
import kotlinx.coroutines.sync.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.stress.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.reflect.*

// This test suit serves two purposes. First of all, it tests the `SegmentQueueSynchronizer`
// implementation under different use-cases and workloads. On the other side, this test suite
// provides different well-known synchronization and communication primitive implementations
// via `SegmentQueueSynchronizer`, which can be considered as an API richness check as well as
// a collection of examples on how to use `SegmentQueueSynchronizer` to build new primitives.

// ########################
// # READERS-WRITER MUTEX #
// ########################

/**
 * This readers-writer mutex maintains two atomic variables [R] and [W], and uses two
 * separate [SegmentQueueSynchronizer]-s for waiting readers and writers. The 64-bit
 * variable [R] maintains three mostly readers-related states atomically:
 * - `WF` (writer's flag) bit that is `true` if there is a writer waiting for the write lock or holding it,
 * - `AR` (active readers) 30-bit counter which represents the number of coroutines holding a read lock,
 * - `WR` (waiting readers) 30-bit counter which represents the number of coroutines waiting for a
 *                          read lock in the corresponding [SegmentQueueSynchronizer].
 * This way, when a reader comes for a lock, it atomically checks whether the `WF` flag is set and
 * either increments the `AR` counter and acquires a lock if it is not set, or increments the
 * `WR` counter and suspends otherwise. At the same time, when a reader releases the lock, it
 * it checks whether it is the last active reader and resumes the first  waiting writer if the `WF`
 * flag is set.
 *
 * Writers, on their side, use an additional [W] field which represents the number of waiting
 * writers as well as several internal flags:
 * - `WW` (waiting writers) 30-bit counter that represents the number of coroutines  waiting for
 *                          the write lock in the corresponding [SegmentQueueSynchronizer],
 * - `WLA` (the write lock is acquired) flag which is `true` when the write lock is acquired,
 *                                      and `WF` should be `true` as well in this case,
 * - `WLRP` (write lock release is in progress) flag which is `true` when the [releaseWrite]
 *                                              invocation is in progress. Note, that `WLA`
 *                                              should already be `false` in this case.
 * - `WRF` (writer is resumed) flag that can be set to `true` by [releaseRead] if there is a
 *                             concurrent [releaseWrite], so that `WLRP` is set to true. This
 *                             flag helps to manage the race when [releaseWrite] successfully
 *                             resumed waiting readers, has not re-set `WF` flag in [R] yet,
 *                             while there readers completed with [releaseRead] and the last
 *                             one observes the `WF` flag set to `true`, so that it should try
 *                             to resume the next waiting writer. However, it is better to tell
 *                             the concurrent [releaseWrite] to check whether there is a writer
 *                             and resume it.
 *
 */
internal class ReadWriteMutex {
    val R = atomic(0L)
    val W = atomic(0)

    val sqsForWriters = object : SegmentQueueSynchronizer<Unit>() {
        override val resumeMode: ResumeMode get() = ASYNC
        override val cancellationMode: CancellationMode get() = SIMPLE // TODO

        override fun onCancellation(): Boolean {
            while (true) {
                val w = curW
                if (w.ww == 0) return false
                if (w.ww > 1 || w.wla) {
                    // just decrement the number of waiting writers
                    if (casW(w, constructW(w.ww - 1, w.wla, w.wlrp, w.wrf))) return true
                } else {
                    if (w.wlrp) return false
                    if (casW(w, constructW(0, false, true, false))) {
                    // Phase 2. Re-set the WF flag
                    // and resume readers if needed.
                    var activeReaders: Boolean
                    while (true) {
                        val r = R.value
                        val wf = r.wf
                        val ra = r.ar
                        val rw = r.wr
                        assert(wf) { "WF should be set here" }
                        // Re-set the WF flag and resume the waiting readers logically.
                        if (R.compareAndSet(r, constructR(false, rw + ra, 0))) {
                            // Were there waiting readers?
                            // Resume them physically if needed.
                            repeat(rw) {
                                val success = sqsForReaders.resume(Unit)
                                assert(success) { "Reader resumption cannot fail because of the smart cancellation in the SQS" }
                            }
                            activeReaders = (ra + rw) > 0
                            break
                        }
                    }
                    // Phase 3. Try to re-set the WLRP flag
                    // if there is no waiting writer.
                    while (true) {
                        val w = W.value
                        val ww = w.ww
                        val wla = w.wla
                        val wlrp = w.wlrp
                        val wrf = w.wrf
                        assert(wlrp) { "WLRP flag should still be set" }
                        assert(!wla) { "There should be no active writer at this point: $this" }
//                        assert(!wrf) { "WRF flag can be set only when the WF flag is put back"}
                        // Is there a waiting writer?
                        if (ww != 0 && !activeReaders) break
                        // No waiting writers, try
                        // to complete immediately.
                        val updW = constructW(0, false, false, false)
                        if (W.compareAndSet(w, updW)) return true
                    }
                        // Phase 4. There is a waiting writer,
                        // set the WF flag back and try to grab
                        // the write lock.
                        var acquired = false
                        while (true) {
                            val r = R.value
                            val wf = r.wf
                            val ar = r.ar
                            val wr = r.wr
                            assert(!wf) { "The WF flag should not be set at this point" }
                            assert(wr == 0) { "The number of waiting readers shold be 0 when the WF flag is not set" }
                            val updR = constructR(true, ar, 0)
                            // Try to set the WF flag.
                            if (!R.compareAndSet(r, updR)) continue
                            // Check whether the write lock is acquired.
                            if (ar == 0) acquired = true
                            break
                        }
                        // Phase 5. Re-set the WLRP flag and try to resume
                        // the next waiting writer if the write lock is grabbed.
                        while (true) {
                            val w = W.value
                            val ww = w.ww
                            val wla = w.wla
                            val wlrp = w.wlrp
                            val wrf = w.wrf
                            assert(ww > 0) { "WW cannot decrease without resumptions" }
                            check(wlrp) { "WLRP flag should still be set" }
                            assert(!wla) { "WLA cannot be set here" }
                            val resume = acquired || wrf
                            val updW = constructW(if (resume) ww - 1 else ww, resume, false, false)
                            if (W.compareAndSet(w, updW)) {
                                if (resume) {
                                    if (!resume(Unit)) releaseWrite()
                                }
                                return true
                            }
                        }
                    }
                }
            }
        }

        override fun tryReturnRefusedValue(value: Unit): Boolean {
            releaseWrite()
            return true
        }
    }

    private val curR get() = R.value
    private val curW get() = W.value
    private fun casR(cur: Long, new: Long) = R.compareAndSet(cur, new)
    private fun casW(cur: Int, new: Int) = W.compareAndSet(cur, new)

    val sqsForReaders = object : SegmentQueueSynchronizer<Unit>() {
        override val resumeMode: ResumeMode get() = ASYNC
        override val cancellationMode: CancellationMode get() = SMART_ASYNC

        override fun onCancellation(): Boolean {
            while (true) {
                val r = curR
                if (r.wr == 0) return false
                if (casR(r, constructR(r.wf, r.ar, r.wr - 1))) {
                    return true
                }
            }
        }

        override fun tryReturnRefusedValue(value: Unit): Boolean {
            releaseRead()
            return true
        }
    }

    suspend fun acquireRead(): Unit = R.loop { r ->
        // Read the current [R] state.
        val wf = r.wf
        val ar = r.ar
        val wr = r.wr
        // Is there an active or waiting writer?
        if (!wf) {
            // There is no writer, try to grab a read lock!
            assert(wr == 0)
            val upd = constructR(wf, ar + 1, wr)
            if (R.compareAndSet(r, upd)) return
        } else {
            // This reader should wait for a lock, try to
            // increment the number of waiting readers and suspend.
            val upd = constructR(wf, ar, wr + 1)
            if (R.compareAndSet(r, upd)) {
                suspendAtomicCancellableCoroutine<Unit> { sqsForReaders.suspend(it) }
                return
            }
        }
    }

    suspend fun acquireWrite() {
        try_again@while (true) {
            // Increment the number of waiting writers at first.
            val w = W.getAndIncrement()
            val ww = w.ww
            val wla = w.wla
            val wlrp = w.wlrp
            // Is this writer the first one? Check whether there are other
            // writers waiting for the lock, an active one, or a concurrent
            // [releaseWrite] invocation is in progress.
            if (wla || wlrp) {
                // Try to suspend and re-try the whole operation on failure.
                var failed = false
                suspendAtomicCancellableCoroutine<Unit> { cont ->
                    if (!sqsForWriters.suspend(cont)) {
                        cont.resume(Unit)
                        failed = true
                    }
                }
                if (failed) continue@try_again
                return
            }
            // This writer is the first one. Set the `WF` flag and
            // complete immediately if there is no reader.
            while (true) {
                val r = R.value
                val wf = r.wf
                val ar = r.ar
                val wr = r.wr
                if (wf) {
                    // Try to suspend and re-try the whole operation on failure.
                    var failed = false
                    suspendAtomicCancellableCoroutine<Unit> { cont ->
                        if (!sqsForWriters.suspend(cont)) {
                            cont.resume(Unit)
                            failed = true
                        }
                    }
                    if (failed) continue@try_again
                    return
                }
                assert(!wf) { "WF flag should not be set at this point: $this" }
                assert(wr == 0) { "The number of waiting readers should be 0 when the WF flag is not set"}
                if (R.compareAndSet(r, constructR(true, ar, wr))) {
                    // Is the lock acquired? Check the number of readers.
                    if (ar == 0) {
                        // Yes! The write lock is just acquired!
                        // Update `W` correspondingly.
                        W.update { w1 ->
                            val ww1 = w1.ww
                            val wla1 = w1.wla
                            val wlrp1 = w1.wlrp
                            val wrf1 = w1.wrf
                            assert(ww1 > 0) { "WW should be greater than 0 at least because of this `acquireWrite` invocation" }
                            assert(!wla1 && !wlrp1 && !wrf1) { "WLA, WLRP, and WRF flags should not be set here" }
                            constructW(ww1 - 1, true, false, false)
                        }
                        return
                    }
                    // There were active readers at the point of `WF` flag placing.
                    // Try to suspend and re-try the whole operation on failure.
                    // Note, that the thread that fails on resumption should
                    // re-set the WF flag if required.
                    var failed = false
                    suspendAtomicCancellableCoroutine<Unit> { cont ->
                        if (!sqsForWriters.suspend(cont)) {
                            cont.resume(Unit)
                            failed = true
                        }
                    }
                    if (failed) continue@try_again
                    return
                }
            }
        }
    }

    fun releaseRead() {
        while (true) {
            // Read the current [R] state
            val r = R.value
            val wf = r.wf
            val ra = r.ar
            val rw = r.wr
            check(ra > 0) { "No active reader to release" }
            // Try to decrement the number of active readers
            val upd = constructR(wf, ra - 1, rw)
            if (!R.compareAndSet(r, upd)) continue
            // Check whether the current reader is the last one,
            // and resume the first writer if the `WF` flag is set.
            if (ra == 1 && wf) onLastReadRelease()
            return
        }
    }

    // TODO rename me
    private fun onLastReadRelease() {
        while (true) {
            // Either WLA, WLA or WLRP should be
            // non-zero when the WF flag is set.
            val w = W.value
            val ww = w.ww
            val wla = w.wla
            val wlrp = w.wlrp
            val wrf = w.wrf
            assert(!wla) { "There should be no active writer at this point" }
            assert(!wrf) { "The WRF flag cannot be set at this point" }
            // Is there still a concurrent [releaseWrite]?
            // Try to delegate the resumption work in this case.
            if (wlrp) {
                val updW = constructW(ww, false, true, true)
                if (W.compareAndSet(w, updW)) return
            } else {
                if (ww == 0) return // cancellation is happening TODO
                assert(ww > 0) { "At most one waiting writer should be registered at this point" }
                // Try to set the `WLA` flag and decrement
                // the number of waiting writers.
                val updW = constructW(ww -1, true, false, false)
                if (!W.compareAndSet(w, updW)) continue
                // Try to resume the first waiting writer.
                if (sqsForWriters.resume(Unit)) return
                // The resumption fails. However, it can be
                // processed as a successful write lock
                // acquisition followed by a release
                // invocation.
                releaseWrite()
                return
            }
        }
    }

    fun releaseWrite() {
        // Phase 1. Try to resume the next waiting writer
        // or re-set the WLA flag and set the WLRP one.
        while (true) {
            val w = W.value
            val ww = w.ww
            val wla = w.wla
            val wlrp = w.wlrp
            val wrf = w.wrf
            check(wla) { "Write lock is not acquired" }
            assert(!wlrp && !wrf) { "WLRP and WRF flags should not be set in the beginning" }
            // Is there a waiting writer?
            if (ww > 0) {
                val updW = constructW(ww - 1, true, false, false)
                if (W.compareAndSet(w, updW) && sqsForWriters.resume(Unit)) return
            } else {
                assert(ww == 0) { "WW can be negative" }
                // Re-set the WLA flag and set the WLRP one.
                val updW = constructW(ww, false, true, false)
                if (W.compareAndSet(w, updW)) break
            }
        }
        completeReleaseWrite()
    }

    private fun completeReleaseWrite() {
        // Phase 2. Re-set the WF flag
        // and resume readers if needed.
        while (true) {
            val r = R.value
            val wf = r.wf
            val ra = r.ar
            val rw = r.wr
            assert(ra == 0) { "There should be no active reader while the write lock is acquired" }
            assert(wf) { "WF should be set here" }
            // Re-set the WF flag and resume the waiting readers logically.
            if (R.compareAndSet(r, constructR(false, rw, 0))) {
                // Were there waiting readers?
                // Resume them physically if needed.
                if (rw > 0) {
                    repeat(rw) {
                        val success = sqsForReaders.resume(Unit)
                        assert(success) { "Reader resumption cannot fail because of the smart cancellation in the SQS" }
                    }
//                    // Decrement the number of active readers
//                    // on the number of failed resumptions.
//                    val rUpd = R.updateAndGet { r1 ->
//                        assert(!r1.wf) { "WF flag cannot be re-set while the WLRP is set" }
//                        constructR(false, r1.ar - failedResumptions, r1.wr)
//                    }
//                    if (rw == 0 && wf) onLastReadRelease()
                }
                break
            }
        }
        // Phase 3. Try to re-set the WLRP flag
        // if there is no waiting writer.
        while (true) {
            val w = W.value
            val ww = w.ww
            val wla = w.wla
            val wlrp = w.wlrp
            val wrf = w.wrf
            assert(wlrp) { "WLRP flag should still be set" }
            assert(!wla) { "There should be no active writer at this point: $this" }
            assert(!wrf) { "WRF flag can be set only when the WF flag is put back"}
            // Is there a waiting writer?
            if (ww != 0) break
            // No waiting writers, try
            // to complete immediately.
            val updW = constructW(0, false, false, false)
            if (W.compareAndSet(w, updW)) return
        }
        // Phase 4. There is a waiting writer,
        // set the WF flag back and try to grab
        // the write lock.
        var acquired = false
        while (true) {
            val r = R.value
            val wf = r.wf
            val ar = r.ar
            val wr = r.wr
            assert(!wf) { "The WF flag should not be set at this point" }
            assert(wr == 0) { "The number of waiting readers shold be 0 when the WF flag is not set" }
            val updR = constructR(true, ar, 0)
            // Try to set the WF flag.
            if (!R.compareAndSet(r, updR)) continue
            // Check whether the write lock is acquired.
            if (ar == 0) acquired = true
            break
        }
        // Phase 5. Re-set the WLRP flag and try to resume
        // the next waiting writer if the write lock is grabbed.
        while (true) {
            val w = W.value
            val ww = w.ww
            val wla = w.wla
            val wlrp = w.wlrp
            val wrf = w.wrf
            assert(ww > 0) { "WW cannot decrease without resumptions" }
            check(wlrp) { "WLRP flag should still be set" }
            assert(!wla) { "WLA cannot be set here" }
            val resume = acquired || wrf
            val updW = constructW(if (resume) ww - 1 else ww, resume, false, false)
            if (W.compareAndSet(w, updW)) {
                if (resume) {
                    if (!sqsForWriters.resume(Unit)) releaseWrite()
                }
                return
            }
        }
    }

    override fun toString() = "R=<${R.value.wf},${R.value.ar},${R.value.wr}>," +
        "W=<${W.value.ww},${W.value.wla},${W.value.wlrp},${W.value.wrf}>"

    companion object {
        inline val Long.wf: Boolean get() = this and WF_BIT != 0L
        const val WF_BIT = 1L shl 62
        inline val Long.R_withWfBit: Long get() = this or WF_BIT
        inline val Long.R_withoutWfBit: Long get() = R_withWfBit - WF_BIT

        inline val Long.wr: Int get() = (this and WAITERS_MASK).toInt()
        const val WAITERS_MASK = (1L shl 30) - 1L

        inline val Long.ar: Int get() = ((this and ACTIVE_MASK) shr 30).toInt()
        const val ACTIVE_MASK = (1L shl 61) - 1L - WAITERS_MASK

        @Suppress("NOTHING_TO_INLINE")
        inline fun constructR(wf: Boolean, ar: Int, wr: Int): Long {
            var res = if (wf) WF_BIT else 0
            res += ar.toLong() shl 30
            res += wr.toLong()
            return res
        }

        const val WRITER_ACTIVE_FLAG: Int = 10_000_000
        const val RELEASE_IN_PROGRESS_FLAG = 100_000_000
        const val WRITER_RESUMED_FLAG = 1_000_000_000

        inline val Int.ww : Int get() = this % WRITER_ACTIVE_FLAG
        inline val Int.wla : Boolean get() = (this / WRITER_ACTIVE_FLAG) % 10 == 1
        inline val Int.wlrp : Boolean get() = (this / RELEASE_IN_PROGRESS_FLAG) % 10 == 1
        inline val Int.wrf : Boolean get() = (this / WRITER_RESUMED_FLAG) % 10 == 1

        inline fun constructW(ww: Int, wla: Boolean, wlrp: Boolean, wrf: Boolean): Int {
            var res = ww
            if (wla) res += WRITER_ACTIVE_FLAG
            if (wlrp) res += RELEASE_IN_PROGRESS_FLAG
            if (wrf) res += WRITER_RESUMED_FLAG
            return res
        }
    }
}

internal class ReadWriteMutexTest : TestBase() {
    @Test
    fun `simple single-coroutine test`() = runTest {
        val m = ReadWriteMutex()
        m.acquireRead()
        m.acquireRead()
        m.releaseRead()
        m.releaseRead()
        m.acquireWrite()
        m.releaseWrite()
        m.acquireRead()
    }

    @Test
    fun `simple multiple coroutines test`() = runTest {
        val m = ReadWriteMutex()
        m.acquireRead()
        expect(1)
        launch {
            expect(2)
            m.acquireRead()
            expect(3)
        }
        yield()
        expect(4)
        launch {
            expect(5)
            m.acquireWrite()
            expect(8)
        }
        yield()
        expect(6)
        m.releaseRead()
        yield()
        expect(7)
        m.releaseRead()
        yield()
        finish(9)
    }

    @Test
    fun `acquireRead suspend after cancelled acquireWrite`() = runTest {
        val m = ReadWriteMutex()
        m.acquireRead()
        val wJob = launch {
            expect(1)
            m.acquireWrite()
            expectUnreached()
        }
        yield()
        expect(2)
        wJob.cancel()
        val rJob = launch {
            expect(3)
            m.acquireRead()
            expectUnreached()
        }
        yield()
        rJob.cancel()
        finish(4)
    }
}

internal class ReadWriteMutexCounterLCStressTest {
    val m = ReadWriteMutex()
    var c = 0

    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true)
    suspend fun inc(): Int = try {
        m.acquireWrite()
        c++
    } finally {
        m.releaseWrite()
    }

    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true)
    suspend fun get(): Int = try {
        m.acquireRead()
        c
    } finally {
        m.releaseRead()
    }

//    @StateRepresentation
//    fun stateRepresentation(): String = "$c+$m"

//    @Test
//    fun test2() = ModelCheckingOptions()
//        .iterations(50)
//        .actorsBefore(0)
//        .actorsAfter(0)
//        .threads(3)
//        .actorsPerThread(4)
//        .logLevel(LoggingLevel.INFO)
//        .invocationsPerIteration(100_000)
//        .sequentialSpecification(ReadWriteMutexCounterSequential::class.java)
//        .check(this::class)

    @Test
    fun test() = StressOptions()
        .actorsBefore(0)
        .actorsAfter(0)
        .threads(3)
        .actorsPerThread(5)
        .invocationsPerIteration(100_000)
        .logLevel(LoggingLevel.INFO)
        .sequentialSpecification(ReadWriteMutexCounterSequential::class.java)
        .check(this::class)
}

class ReadWriteMutexCounterSequential : VerifierState() {
    var c = 0
    suspend fun inc() = c++
    suspend fun get() = c

    override fun extractState() = c
}

class ReadWriteMutexLCStressTest {
    private val m = ReadWriteMutex()
    private val readLockAcquired = IntArray(6)
    private val writeLockAcquired = BooleanArray(6)

    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true)
    suspend fun acquireRead(@Param(gen = ThreadIdGen::class) threadId: Int) {
        m.acquireRead()
        readLockAcquired[threadId]++
    }

    @Operation(cancellableOnSuspension = false, allowExtraSuspension = true)
    suspend fun acquireWrite(@Param(gen = ThreadIdGen::class) threadId: Int) {
        m.acquireWrite()
        assert(!writeLockAcquired[threadId]) { "The mutex is not reentrant" }
        writeLockAcquired[threadId] = true
    }

    @Operation
    fun releaseRead(@Param(gen = ThreadIdGen::class) threadId: Int): Boolean {
        if (readLockAcquired[threadId] == 0) return false
        m.releaseRead()
        readLockAcquired[threadId]--
        return true
    }

    @Operation
    fun releaseWrite(@Param(gen = ThreadIdGen::class) threadId: Int): Boolean {
        if (!writeLockAcquired[threadId]) return false
        m.releaseWrite()
        writeLockAcquired[threadId] = false
        return true
    }

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .actorsAfter(0)
        .threads(3)
        .actorsPerThread(3)
        .invocationsPerIteration(500_000)
        .logLevel(LoggingLevel.INFO)
        .sequentialSpecification(ReadWriteMutexSequential::class.java)
        .check(this::class)

//    @Test
//    fun test() = ModelCheckingOptions()
//        .iterations(20)
//        .actorsBefore(0)
//        .actorsAfter(0)
//        .threads(3)
//        .actorsPerThread(3)
//        .logLevel(LoggingLevel.INFO)
//        .invocationsPerIteration(100_000)
//        .sequentialSpecification(ReadWriteMutexSequential::class.java)
//        .check(this::class)

//    @StateRepresentation
//    fun stateRepresentation() = m.toString()
}

class ReadWriteMutexSequential : VerifierState() {
    private var activeReaders = 0
    private var writeLockedOrWaiting = false
    private val waitingReaders = ArrayList<CancellableContinuation<Unit>>()
    private val waitingWriters = ArrayList<CancellableContinuation<Unit>>()
    // Thread-local info
    private val readLockAcquired = IntArray(6)
    private val writeLockAcquired = BooleanArray(6)

    suspend fun acquireRead(threadId: Int) {
        if (writeLockedOrWaiting) {
            suspendAtomicCancellableCoroutine<Unit> { cont ->
                waitingReaders.add(cont)
            }
        } else {
            activeReaders++
        }
        readLockAcquired[threadId]++
    }

    suspend fun acquireWrite(threadId: Int) {
        if (activeReaders > 0 || writeLockedOrWaiting) {
            writeLockedOrWaiting = true
            suspendAtomicCancellableCoroutine<Unit> { cont ->
                waitingWriters.add(cont)
            }
        } else {
            writeLockedOrWaiting = true
        }
        writeLockAcquired[threadId] = true
    }

    fun releaseRead(threadId: Int): Boolean {
        if (readLockAcquired[threadId] == 0) return false
        readLockAcquired[threadId]--
        activeReaders--
        if (activeReaders == 0 && writeLockedOrWaiting) {
            while (waitingWriters.isNotEmpty()) {
                val w = waitingWriters.removeAt(0)
                if (w.tryResume0(Unit)) return true
            }
            writeLockedOrWaiting = false
            val resumedReaders = waitingReaders.map { it.tryResume0(Unit) }.filter { it }.count()
            waitingReaders.clear()
            activeReaders = resumedReaders
            return true
        }
        return true
    }

    fun releaseWrite(threadId: Int): Boolean {
        if (!writeLockAcquired[threadId]) return false
        writeLockAcquired[threadId] = false
        while (waitingWriters.isNotEmpty()) {
            val w = waitingWriters.removeAt(0)
            if (w.tryResume0(Unit)) return true
        }
        writeLockedOrWaiting = false
        val resumedReaders = waitingReaders.map { it.tryResume0(Unit) }.filter { it }.count()
        waitingReaders.clear()
        activeReaders = resumedReaders
        return true
    }

    override fun extractState() = "$activeReaders, $writeLockedOrWaiting, ${readLockAcquired.contentToString()}, ${writeLockAcquired.contentToString()}"
}

// ##############
// # SEMAPHORES #
// ##############

/**
 * This [Semaphore] implementation is similar to the one in the library,
 * but uses the [asynchronous][ASYNC] mode for resumptions. However,
 * it is hard to make [tryAcquire] linearizable in this case, so that
 * it is simply not supported here.
 */
internal class AsyncSemaphore(permits: Int) : SegmentQueueSynchronizer<Unit>(), Semaphore {
    override val resumeMode get() = ASYNC

    private val _availablePermits = atomic(permits)
    override val availablePermits get() = _availablePermits.value.coerceAtLeast(0)

    override fun tryAcquire() =  error("Not supported in the ASYNC version")

    override suspend fun acquire() {
        // Decrement the number of available permits.
        val p = _availablePermits.getAndDecrement()
        // Is the permit successfully acquired?
        if (p > 0) return
        // Suspend otherwise.
        suspendAtomicCancellableCoroutine<Unit> { cont ->
            check(suspend(cont)) { "Should not fail in ASYNC mode" }
        }
    }

    override fun release() {
        while (true) {
            // Increment the number of available permits.
            val p = _availablePermits.getAndIncrement()
            // Is there a waiter that should be resumed?
            if (p >= 0) return
            // Try to resume the first waiter, and
            // re-start the operation if it is cancelled.
            if (resume(Unit)) return
        }
    }
}

/**
 * This semaphore implementation is correct only if [release] is always
 * invoked after a successful [acquire]; in other words, when semaphore
 * is used properly, without unexpected [release] invocations. The main
 * advantage is using smart cancellation, so that [release] always works
 * in constant time under no contention, and the cancelled [acquire]
 * requests do not play any role. It is worth noting, that it is possible
 * to make this implementation correct under not atomic but strong cancellation
 * model, when continuation can be cancelled if it is logically resumed
 * but not dispatched yet.
 */
internal class AsyncSemaphoreSmart(permits: Int) : SegmentQueueSynchronizer<Unit>(), Semaphore {
    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART_SYNC

    private val _availablePermits = atomic(permits)
    override val availablePermits get() = _availablePermits.value.coerceAtLeast(0)

    override fun tryAcquire() = error("Not supported in the ASYNC version")

    override suspend fun acquire() {
        // Decrement the number of available permits.
        val p = _availablePermits.getAndDecrement()
        // Is the permit acquired?
        if (p > 0) return
        // Suspend otherwise.
        suspendAtomicCancellableCoroutine<Unit> { cont ->
            check(suspend(cont)) { "Should not fail in ASYNC mode" }
        }
    }

    override fun release() {
        // Increment the number of available permits.
        val p = _availablePermits.getAndIncrement()
        // Is there a waiter that should be resumed?
        if (p >= 0) return
        // Resume the first waiter. Due to the smart
        // cancellation it is possible that this
        // permit will be refused, so that the real
        // release can come with a small lag, but it
        // is guaranteed to be processed eventually.
        resume(Unit)
    }

    override fun onCancellation(): Boolean {
        // Increment the number of available permits.
        val p = _availablePermits.getAndIncrement()
        // Return `true` if there is no `release` which
        // is going to resume us and cannot skip us and
        // resume the next waiter.
        return p < 0
    }
}

/**
 * This implementation is similar to the previous one, but uses [synchronous][SYNC]
 * resumption mode, so that it is possible to implement [tryAcquire] atomically.
 * The only notable difference happens when a permit to be released is refused,
 * and the following [resume] attempt in the cancellation handler fails due to
 * the synchronization on resumption, so that the permit is going to be returned
 * back to the semaphore in [returnValue] function.
 */
internal class SyncSemaphoreSmart(permits: Int) : SegmentQueueSynchronizer<Boolean>(), Semaphore {
    override val resumeMode get() = SYNC
    override val cancellationMode get() = SMART_SYNC

    private val _availablePermits = atomic(permits)
    override val availablePermits get() = _availablePermits.value.coerceAtLeast(0)

    override suspend fun acquire() {
        while (true) {
            // Decrement the number of available permits.
            val p = _availablePermits.getAndDecrement()
            // Is the permit acquired?
            if (p > 0) return
            // Try to suspend otherwise.
            val acquired = suspendAtomicCancellableCoroutine<Boolean> { cont ->
                if (!suspend(cont)) cont.resume(false)
            }
            if (acquired) return
        }
    }

    override fun tryAcquire(): Boolean = _availablePermits.loop { cur ->
        // Try to decrement the number of available
        // permits if it is greater than zero.
        if (cur <= 0) return false
        if (_availablePermits.compareAndSet(cur, cur -1)) return true
    }

    override fun release() {
        while (true) {
            // Increment the number of available permits.
            val p = _availablePermits.getAndIncrement()
            // Is there a waiter that should be resumed?
            if (p >= 0) return
            // Try to resume the first waiter, can fail
            // according to the SYNC mode contract.
            if (resume(true)) return
        }
    }

    override fun onCancellation(): Boolean {
        // Increment the number of available permits.
        val p = _availablePermits.getAndIncrement()
        // Return `true` if there is no `release` which
        // is going to resume us and cannot skip us and
        // resume the next waiter.
        return p < 0
    }

    override fun returnValue(value: Boolean) {
        // Simply release the permit.
        release()
    }
}

abstract class AsyncSemaphoreLCStressTestBase(semaphore: Semaphore, val seqSpec: KClass<*>) {
    private val s = semaphore

    @Operation
    suspend fun acquire() = s.acquire()

    @Operation
    fun release() = s.release()

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .sequentialSpecification(seqSpec.java)
        .check(this::class)
}

class SemaphoreUnboundedSequential1 : SemaphoreSequential(1, false)
class SemaphoreUnboundedSequential2 : SemaphoreSequential(2, false)

class AsyncSemaphore1LCStressTest : AsyncSemaphoreLCStressTestBase(AsyncSemaphore(1), SemaphoreUnboundedSequential1::class)
class AsyncSemaphore2LCStressTest : AsyncSemaphoreLCStressTestBase(AsyncSemaphore(2), SemaphoreUnboundedSequential2::class)

class AsyncSemaphoreSmart1LCStressTest : AsyncSemaphoreLCStressTestBase(AsyncSemaphoreSmart(1), SemaphoreUnboundedSequential1::class)
class AsyncSemaphoreSmart2LCStressTest : AsyncSemaphoreLCStressTestBase(AsyncSemaphoreSmart(2), SemaphoreUnboundedSequential2::class)

class SyncSemaphoreSmart1LCStressTest : SemaphoreLCStressTestBase(SyncSemaphoreSmart(1), SemaphoreUnboundedSequential1::class)
class SyncSemaphoreSmart2LCStressTest : SemaphoreLCStressTestBase(SyncSemaphoreSmart(2), SemaphoreUnboundedSequential2::class)


// ####################################
// # COUNT-DOWN-LATCH SYNCHRONIZATION #
// ####################################

/**
 * This primitive allows to wait until several operation are completed.
 * It is initialized with a given count, and each [countDown] invocation
 * decrements the count of remaining operations to be completed. At the
 * same time, [await] waits until the count reaches zero.
 *
 * This implementation uses simple cancellation, so that the [countDown]
 * invocation that reaches the counter zero works in a linear of the number of [await]
 * invocations, including the ones that are already cancelled.
 */
internal open class CountDownLatch(count: Int) : SegmentQueueSynchronizer<Unit>() {
    override val resumeMode get() = ASYNC

    private val count = atomic(count)
    // The number of suspended `await` invocation.
    // DONE_MARK should be set when the count reaches
    // zero, so that the following suspension attempts
    // can fail and complete immediately.
    private val waiters = atomic(0)

    protected fun decWaiters() = waiters.decrementAndGet()

    /**
     * Decrements the count and resumes waiting
     * [await] invocations if it reaches zero.
     */
    fun countDown() {
        // Decrement the count.
        val r = count.decrementAndGet()
        // Should the waiters be resumed?
        if (r <= 0) resumeWaiters()
    }

    private fun resumeWaiters() {
        val w = waiters.getAndUpdate { cur ->
            // Is the done mark set?
            if (cur and DONE_MARK != 0) return
            cur or DONE_MARK
        }
        // This thread has successfully set
        // the mark, resume the waiters.
        repeat(w) { resume(Unit) }
    }

    /**
     * Waits until the count reaches zero,
     * completes immediately if it is already zero.
     */
    suspend fun await() {
        // Check whether the count has been reached zero,
        // this can be considered as an optimization.
        if (remaining() == 0) return
        // Increment the number of waiters and check
        // that DONE_MARK is not set, finish otherwise.
        val w = waiters.incrementAndGet()
        if (w and DONE_MARK != 0) return
        // The number of waiters is
        // successfully incremented, suspend.
        suspendAtomicCancellableCoroutine<Unit> { suspend(it) }
    }

    /**
     * Return the current count.
     */
    fun remaining(): Int = count.value.coerceAtLeast(0)

    protected companion object {
        const val DONE_MARK = 1 shl 31
    }
}

/**
 * This implementation uses a smarter cancellation mechanism, so that the
 * [countDown] invocation that reaches the counter zero works in linear of
 * the number of non-cancelled [await] invocations. This way, it does not matter
 * how many [await] requests has been cancelled -- they do not play any role.
 */
internal class CountDownLatchSmart(count: Int) : CountDownLatch(count) {
    override val cancellationMode get() = SMART_ASYNC

    override fun onCancellation(): Boolean {
        // Decrement the number of waiters.
        val w = decWaiters()
        // Succeed if the DONE_MARK is not set yet.
        return (w and DONE_MARK) == 0
    }
}

internal abstract class CountDownLatchLCStressTestBase(val cdl: CountDownLatch, val seqSpec: KClass<*>) {
    @Operation
    fun countDown() = cdl.countDown()

    @Operation
    fun remaining() = cdl.remaining()

    @Operation
    suspend fun await() = cdl.await()

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .actorsAfter(0)
        .sequentialSpecification(seqSpec.java)
        .check(this::class)
}

class CountDownLatchSequential1 : CountDownLatchSequential(1)
class CountDownLatchSequential2 : CountDownLatchSequential(2)

internal class CountDownLatch1LCStressTest : CountDownLatchLCStressTestBase(CountDownLatch(1), CountDownLatchSequential1::class)
internal class CountDownLatch2LCStressTest : CountDownLatchLCStressTestBase(CountDownLatch(2), CountDownLatchSequential2::class)

internal class CountDownLatchSmart1LCStressTest : CountDownLatchLCStressTestBase(CountDownLatchSmart(1), CountDownLatchSequential1::class)
internal class CountDownLatchSmart2LCStressTest : CountDownLatchLCStressTestBase(CountDownLatchSmart(2), CountDownLatchSequential2::class)

open class CountDownLatchSequential(initialCount: Int) : VerifierState() {
    private var count = initialCount
    private val waiters = ArrayList<CancellableContinuation<Unit>>()

    fun countDown() {
        if (--count == 0) {
            waiters.forEach { it.tryResume0(Unit) }
            waiters.clear()
        }
    }

    suspend fun await() {
        if (count <= 0) return
        suspendAtomicCancellableCoroutine<Unit> { cont ->
            waiters.add(cont)
        }
    }

    fun remaining(): Int = count.coerceAtLeast(0)

    override fun extractState() = remaining()
}


// ###########################
// # BARRIER SYNCHRONIZATION #
// ###########################

/**
 * This synchronization primitive allows a set of coroutines to
 * all wait for each other to reach a common barrier point.
 *
 * The implementation is straightforward: it maintains a counter
 * of arrived coroutines and increments it in the beginning of
 * [arrived] operation. The last coroutines should resume all the
 * previous ones.
 *
 * In case of cancellation, the handler decrements the counter if
 * not all the parties are arrived. However, it is impossible to
 * make cancellation atomic (e.g., Java's implementation simply
 * does not work in case of thread interruption) since there is
 * no way to resume a set of coroutines atomically. Thus,
 * this implementation is non-atomic if cancellation happens
 * simultaneously to the last [arrive], but is correct under
 * the strong cancellation model, when continuation can be
 * cancelled if it is logically resumed but not dispatched yet.
 */
internal class Barrier(private val parties: Int) : SegmentQueueSynchronizer<Unit>() {
    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART_ASYNC

    // The number of coroutines arrived to this barrier point.
    private val arrived = atomic(0L)

    /**
     * Waits for other parties and returns `true`.
     * Fails if this invocation exceeds the number
     * of parties, returns `false` in this case.
     */
    suspend fun arrive(): Boolean {
        // Increment the number of arrived parties.
        val a = arrived.incrementAndGet()
        return when {
            // Should we suspend?
            a < parties -> {
                suspendCoroutine<Unit> { cont -> suspend(cont) }
                true
            }
            // Are we the last party?
            a == parties.toLong() -> {
                // Resume all waiters.
                repeat(parties - 1) {
                    resume(Unit)
                }
                true
            }
            // Should we fail?
            else -> false
        }
    }

    override fun onCancellation(): Boolean {
        // Decrement the number of arrived parties if possible.
        arrived.loop { cur ->
            // Are we going to be resumed?
            // The resumption permit should be refused in this case.
            if (cur == parties.toLong()) return false
            // Successful cancellation, return `true`.
            if (arrived.compareAndSet(cur, cur - 1)) return true
        }
    }
}

// TODO: non-atomic cancellation test, the corresponding feature in lincheck is required.
abstract class BarrierLCStressTestBase(parties: Int, val seqSpec: KClass<*>) {
    private val b = Barrier(parties)

    @Operation(cancellableOnSuspension = false)
    suspend fun arrive() = b.arrive()

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .actorsAfter(0)
        .threads(3)
        .sequentialSpecification(seqSpec.java)
        .check(this::class)
}

class BarrierSequential1 : BarrierSequential(1)
class Barrier1LCStressTest : BarrierLCStressTestBase(1, BarrierSequential1::class)
class BarrierSequential2 : BarrierSequential(2)
class Barrier2LCStressTest : BarrierLCStressTestBase(2, BarrierSequential2::class)
class BarrierSequential3 : BarrierSequential(3)
class Barrier3LCStressTest : BarrierLCStressTestBase(3, BarrierSequential3::class)

open class BarrierSequential(parties: Int) : VerifierState() {
    private var remainig = parties
    private val waiters = ArrayList<Continuation<Unit>>()

    suspend fun arrive(): Boolean {
        val r = --remainig
        return when {
            r > 0 -> {
                suspendAtomicCancellableCoroutine<Unit> { cont ->
                    waiters.add(cont)
                    cont.invokeOnCancellation {
                        remainig++
                        waiters.remove(cont)
                    }
                }
                true
            }
            r == 0 -> {
                waiters.forEach { it.resume(Unit) }
                true
            }
            else -> false
        }
    }

    override fun extractState() = remainig > 0
}


// ##################
// # BLOCKING POOLS #
// ##################

/**
 * While using resources such as database connections, sockets, etc.,
 * it is typical to reuse them; that requires a fast and handy mechanism.
 * This [BlockingPool] abstraction maintains a set of elements that can be put
 * into the pool for further reuse or be retrieved to process the current operation.
 * When [retrieve] comes to an empty pool, it blocks, and the following [put] operation
 * resumes it; all the waiting requests are processed in the first-in-first-out (FIFO) order.
 *
 * In our tests we consider two pool implementations: the [queue-based][BlockingQueuePool]
 * and the [stack-based][BlockingStackPool]. Intuitively, the queue-based implementation is
 * faster since it is built on arrays and uses `Fetch-And-Add`-s on the contended path,
 * while the stack-based pool retrieves the last inserted, thus the "hottest", elements.
 *
 * Please note that both these implementations are not atomic and can retrieve elements
 * out-of-order under some races. However, since pools by themselves do not guarantee
 * that the stored elements are ordered (the one may consider them as bags),
 * these queue- and stack-based versions should be considered as pools with specific heuristics.
 */
interface BlockingPool<T: Any> {
    /**
     * Either resumes the first waiting [retrieve] operation
     * and passes the [element] to it, or simply put the
     * [element] into the pool.
     */
    fun put(element: T)

    /**
     * Retrieves one of the elements from the pool
     * (the order is not specified), or suspends if it is
     * empty -- the following [put] operations resume
     * waiting [retrieve]-s in the first-in-first-out order.
     */
    suspend fun retrieve(): T
}

/**
 * This pool uses queue under the hood and implemented withing the simple cancellation technique.
 */
internal class BlockingQueuePool<T: Any> : SegmentQueueSynchronizer<T>(), BlockingPool<T> {
    override val resumeMode get() = ASYNC

    // > 0 -- number of elements;
    // = 0 -- empty pool;
    // < 0 -- number of waiters.
    private val availableElements = atomic(0L)

    // This is an infinite array by design, a plain array is used for simplicity.
    private val elements = atomicArrayOfNulls<Any?>(100)

    // Indices in [elements]  for the next [tryInsert] and [tryRetrieve] operations.
    // Each [tryInsert]/[tryRetrieve] pair works on a separate slot. When [tryRetrieve]
    // comes earlier, it marks the slot as [BROKEN] so that both this operation and the
    // corresponding [tryInsert] fail.
    private val insertIdx = atomic(0)
    private val retrieveIdx = atomic(0)

    override fun put(element: T) {
        while (true) {
            // Increment the number of elements in advance.
            val b = availableElements.getAndIncrement()
            // Is there a waiting `retrieve`?
            if (b < 0) {
                // Try to resume the first waiter,
                // can fail if it is already cancelled.
                if (resume(element)) return
            } else {
                // Try to insert the element into the
                // queue, can fail if the slot is broken.
                if (tryInsert(element)) return
            }
        }
    }

    /**
     * Tries to insert the [element] into the next
     * [elements] array slot. Returns `true` if
     * succeeds, or `false` if the slot is [broken][BROKEN].
     */
    private fun tryInsert(element: T): Boolean {
        val i = insertIdx.getAndIncrement()
        return elements[i].compareAndSet(null, element)
    }

    override suspend fun retrieve(): T {
        while (true) {
            // Decrements the number of elements.
            val b = availableElements.getAndDecrement()
            // Is there an element in the pool?
            if (b > 0) {
                // Try to retrieve the first element,
                // can fail if the first [elements] slot
                // is empty due to a race.
                val x = tryRetrieve()
                if (x != null) return x
            } else {
                // The pool is empty, suspend.
                return suspendAtomicCancellableCoroutine { cont ->
                    suspend(cont)
                }
            }
        }
    }

    /**
     * Tries to retrieve the first element from
     * the [elements] array. Returns the element if
     * succeeds, or `null` if the first slot is empty
     * due to a race -- it marks the slot as [broken][BROKEN]
     * in this case, so that the corresponding [tryInsert]
     * invocation fails.
     */
    private fun tryRetrieve(): T? {
        val i = retrieveIdx.getAndIncrement()
        return elements[i].getAndSet(BROKEN) as T?
    }

    companion object {
        @JvmStatic
        val BROKEN = Symbol("BROKEN")
    }
}

/**
 * This pool uses stack under the hood and shows how to use smart cancellation
 * for such data structures with resources.
 */
internal class BlockingStackPool<T: Any> : SegmentQueueSynchronizer<T>(), BlockingPool<T> {
    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART_SYNC

    // The stack is implemented via a concurrent linked list,
    // this is its head; `null` means that the stack is empty.
    private val head = atomic<StackNode<T>?>(null)

    // > 0 -- number of elements;
    // = 0 -- empty pool;
    // < 0 -- number of waiters.
    private val availableElements = atomic(0)

    override fun put(element: T) {
        while (true) {
            // Increment the number of elements in advance.
            val b = availableElements.getAndIncrement()
            // Is there a waiting retrieve?
            if (b < 0) {
                // Resume the first waiter, never fails
                // in the smart cancellation mode.
                resume(element)
                return
            } else {
                // Try to insert the element into the
                // stack, can fail if a concurrent [tryRetrieve]
                // came earlier and marked it with a failure node.
                if (tryInsert(element)) return
            }
        }
    }

    /**
     * Tries to insert the [element] into the stack.
     * Returns `true` on success`, or `false` if the
     * stack is marked with a failure node, retrieving
     * it in this case.
     */
    private fun tryInsert(element: T): Boolean = head.loop { h ->
        // Is the stack marked with a failure node?
        if (h != null && h.element == null) {
            // Try to retrieve the failure node.
            if (head.compareAndSet(h, h.next)) return false
        } else {
            // Try to insert the element.
            val newHead = StackNode(element, h)
            if (head.compareAndSet(h, newHead)) return true
        }
    }

    override suspend fun retrieve(): T {
        while (true) {
            // Decrement the number of elements.
            val b = availableElements.getAndDecrement()
            // Is there an element in the pool?
            if (b > 0) {
                // Try to retrieve the top element,
                // can fail if the stack if empty
                // due to a race.
                val x = tryRetrieve()
                if (x != null) return x
            } else {
                // The pool is empty, suspend.
                return suspendAtomicCancellableCoroutine { cont ->
                    suspend(cont)
                }
            }
        }
    }

    /**
     * Try to retrieve the top (last) element and return `true`
     * if the stack is not empty, or return `false` and
     * insert a failure node otherwise.
     */
    private fun tryRetrieve(): T? = head.loop { h ->
        // Is the queue empty or full of failure nodes?
        if (h == null || h.element == null) {
            // Try to add one more failure node and fail.
            val failNode = StackNode(null, h)
            if (head.compareAndSet(h, failNode)) return null
        } else {
            // Try to retrieve the top element.
            if (head.compareAndSet(h, h.next)) return h.element
        }
    }

    // The logic of cancellation is very similar to the one
    // in semaphore, with the only difference that elements
    // should be physically returned to the pool.
    override fun onCancellation(): Boolean {
        val b = availableElements.getAndIncrement()
        return b < 0
    }

    // If an element is refused, it should be inserted back to the stack.
    override fun tryReturnRefusedValue(value: T) = tryInsert(value)

    // In order to return the value back
    // to the pool [put] is naturally used.
    override fun returnValue(value: T) = put(value)

    class StackNode<T>(val element: T?, val next: StackNode<T>?)
}

abstract class BlockingPoolLCStressTestBase(val p: BlockingPool<Unit>) {
    @Operation
    fun put() = p.put(Unit)

    @Operation
    suspend fun retrieve() = p.retrieve()

    @Test
    fun test() = LCStressOptionsDefault()
        .sequentialSpecification(BlockingPoolUnitSequential::class.java)
        .check(this::class)
}
class BlockingQueuePoolLCStressTest : BlockingPoolLCStressTestBase(BlockingQueuePool())
class BlockingStackPoolLCStressTest : BlockingPoolLCStressTestBase(BlockingStackPool())

class BlockingPoolUnitSequential : VerifierState() {
    private var elements = 0
    private val waiters = ArrayList<CancellableContinuation<Unit>>()

    fun put() {
        while (true) {
            if (waiters.isNotEmpty()) {
                val w = waiters.removeAt(0)
                if (w.tryResume0(Unit)) return
            } else {
                elements ++
                return
            }
        }
    }

    suspend fun retrieve() {
        if (elements > 0) {
            elements--
        } else {
            suspendAtomicCancellableCoroutine<Unit> { cont ->
                waiters.add(cont)
            }
        }
    }

    override fun extractState() = elements
}


// #############
// # UTILITIES #
// #############

/**
 * Tries to resume this continuation atomically,
 * returns `true` if succeeds and `false` otherwise.
 */
private fun <T> CancellableContinuation<T>.tryResume0(value: T): Boolean {
    val token = tryResume(value) ?: return false
    completeResume(token)
    return true
}