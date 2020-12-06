package com.naumov;

import com.naumov.cs.counter.Counter;
import com.naumov.cs.counter.CounterWithLock;
import com.naumov.lock.Lock;
import com.naumov.lock.TASLock;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

@BenchmarkMode(Mode.Throughput)
@Warmup(iterations = 5)
@Measurement(iterations = 5)
@Fork(1)
public class TASLockPerformanceTest {
    @State(Scope.Benchmark)
    public static class CounterState {
        final Lock lock = new TASLock();
        final Counter counter = new CounterWithLock(0, lock);
    }

    @Benchmark
    @Group("ConcurrentCounter")
    @GroupThreads(8)
    public void increments(final CounterState state) {
        state.counter.getAndIncrement();
    }

    @Benchmark
    @Group("ConcurrentCounter")
    @GroupThreads(8)
    public void gets(final CounterState state) {
        state.counter.get();
    }

    public static void main(String[] args) throws RunnerException {
        final Options options = new OptionsBuilder()
                .include(TASLockPerformanceTest.class.getName())
                .forks(1)
                .build();

        new Runner(options).run();
    }
}
