/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.commons.math3.stat.descriptive;

import java.io.Serializable;
import java.util.Collection;
import java.util.Iterator;

import org.apache.commons.math3.exception.NullArgumentException;

/**
 * <p>
 * An aggregator for {@code SummaryStatistics} from several data sets or
 * data set partitions.  In its simplest usage mode, the client creates an
 * instance via the zero-argument constructor, then uses
 * {@link #createContributingStatistics()} to obtain a {@code SummaryStatistics}
 * for each individual data set / partition.  The per-set statistics objects
 * are used as normal, and at any time the aggregate statistics for all the
 * contributors can be obtained from this object.
 * </p><p>
 * Clients with specialized requirements can use alternative constructors to
 * control the statistics implementations and initial values used by the
 * contributing and the internal aggregate {@code SummaryStatistics} objects.
 * </p><p>
 * A static {@link #aggregate(Collection)} method is also included that computes
 * aggregate statistics directly from a Collection of SummaryStatistics instances.
 * </p><p>
 * When {@link #createContributingStatistics()} is used to create SummaryStatistics
 * instances to be aggregated concurrently, the created instances'
 * {@link SummaryStatistics#addValue(double)} methods must synchronize on the aggregating
 * instance maintained by this class.  In multithreaded environments, if the functionality
 * provided by {@link #aggregate(Collection)} is adequate, that method should be used
 * to avoid unnecessary computation and synchronization delays.</p>
 *
 * @since 2.0
 *
 */
public class AggregateSummaryStatistics implements StatisticalSummary,
        Serializable {


    /** Serializable version identifier */
    private static final long serialVersionUID = -8207112444016386906L;

    /**
     * A SummaryStatistics serving as a prototype for creating SummaryStatistics
     * contributing to this aggregate
     */
    private final SummaryStatistics statisticsPrototype;

    /**
     * The SummaryStatistics in which aggregate statistics are accumulated.
     */
    private final SummaryStatistics statistics;

    /**
     * Initializes a new AggregateSummaryStatistics with default statistics
     * implementations.
     *
     */
    public AggregateSummaryStatistics() {
        // No try-catch or throws NAE because arg is guaranteed non-null
        this(new SummaryStatistics());
    }

    /**
     * Initializes a new AggregateSummaryStatistics with the specified statistics
     * object as a prototype for contributing statistics and for the internal
     * aggregate statistics.  This provides for customized statistics implementations
     * to be used by contributing and aggregate statistics.
     *
     * @param prototypeStatistics a {@code SummaryStatistics} serving as a
     *      prototype both for the internal aggregate statistics and for
     *      contributing statistics obtained via the
     *      {@code createContributingStatistics()} method.  Being a prototype
     *      means that other objects are initialized by copying this object's state.
     *      If {@code null}, a new, default statistics object is used.  Any statistic
     *      values in the prototype are propagated to contributing statistics
     *      objects and (once) into these aggregate statistics.
     * @throws NullArgumentException if prototypeStatistics is null
     * @see #createContributingStatistics()
     */
    public AggregateSummaryStatistics(SummaryStatistics prototypeStatistics) throws NullArgumentException {
        this(prototypeStatistics,
             prototypeStatistics == null ? null : new SummaryStatistics(prototypeStatistics));
    }

    /**
     * Initializes a new AggregateSummaryStatistics with the specified statistics
     * object as a prototype for contributing statistics and for the internal
     * aggregate statistics.  This provides for different statistics implementations
     * to be used by contributing and aggregate statistics and for an initial
     * state to be supplied for the aggregate statistics.
     *
     * @param prototypeStatistics a {@code SummaryStatistics} serving as a
     *      prototype both for the internal aggregate statistics and for
     *      contributing statistics obtained via the
     *      {@code createContributingStatistics()} method.  Being a prototype
     *      means that other objects are initialized by copying this object's state.
     *      If {@code null}, a new, default statistics object is used.  Any statistic
     *      values in the prototype are propagated to contributing statistics
     *      objects, but not into these aggregate statistics.
     * @param initialStatistics a {@code SummaryStatistics} to serve as the
     *      internal aggregate statistics object.  If {@code null}, a new, default
     *      statistics object is used.
     * @see #createContributingStatistics()
     */
    public AggregateSummaryStatistics(SummaryStatistics prototypeStatistics,
                                      SummaryStatistics initialStatistics) {
        this.statisticsPrototype =
            (prototypeStatistics == null) ? new SummaryStatistics() : prototypeStatistics;
        this.statistics =
            (initialStatistics == null) ? new SummaryStatistics() : initialStatistics;
    }

    /**
     * {@inheritDoc}.  This version returns the maximum over all the aggregated
     * data.
     *
     * @see StatisticalSummary#getMax()
     */
    public double getMax() {
        synchronized (statistics) {
            return statistics.getMax();
        }
    }

    /**
     * {@inheritDoc}.  This version returns the mean of all the aggregated data.
     *
     * @see StatisticalSummary#getMean()
     */
    public double getMean() {
        synchronized (statistics) {
            return statistics.getMean();
        }
    }

    /**
     * {@inheritDoc}.  This version returns the minimum over all the aggregated
     * data.
     *
     * @see StatisticalSummary#getMin()
     */
    public double getMin() {
        synchronized (statistics) {
            return statistics.getMin();
        }
    }

    /**
     * {@inheritDoc}.  This version returns a count of all the aggregated data.
     *
     * @see StatisticalSummary#getN()
     */
    public long getN() {
        synchronized (statistics) {
            return statistics.getN();
        }
    }

    /**
     * {@inheritDoc}.  This version returns the standard deviation of all the
     * aggregated data.
     *
     * @see StatisticalSummary#getStandardDeviation()
     */
    public double getStandardDeviation() {
        synchronized (statistics) {
            return statistics.getStandardDeviation();
        }
    }

    /**
     * {@inheritDoc}.  This version returns a sum of all the aggregated data.
     *
     * @see StatisticalSummary#getSum()
     */
    public double getSum() {
        synchronized (statistics) {
            return statistics.getSum();
        }
    }

    /**
     * {@inheritDoc}.  This version returns the variance of all the aggregated
     * data.
     *
     * @see StatisticalSummary#getVariance()
     */
    public double getVariance() {
        synchronized (statistics) {
            return statistics.getVariance();
        }
    }

    /**
     * Returns the sum of the logs of all the aggregated data.
     *
     * @return the sum of logs
     * @see SummaryStatistics#getSumOfLogs()
     */
    public double getSumOfLogs() {
        synchronized (statistics) {
            return statistics.getSumOfLogs();
        }
    }

    /**
     * Returns the geometric mean of all the aggregated data.
     *
     * @return the geometric mean
     * @see SummaryStatistics#getGeometricMean()
     */
    public double getGeometricMean() {
        synchronized (statistics) {
            return statistics.getGeometricMean();
        }
    }

    /**
     * Returns the sum of the squares of all the aggregated data.
     *
     * @return The sum of squares
     * @see SummaryStatistics#getSumsq()
     */
    public double getSumsq() {
        synchronized (statistics) {
            return statistics.getSumsq();
        }
    }

    /**
     * Returns a statistic related to the Second Central Moment.  Specifically,
     * what is returned is the sum of squared deviations from the sample mean
     * among the all of the aggregated data.
     *
     * @return second central moment statistic
     * @see SummaryStatistics#getSecondMoment()
     */
    public double getSecondMoment() {
        synchronized (statistics) {
            return statistics.getSecondMoment();
        }
    }

    /**
     * Return a {@link StatisticalSummaryValues} instance reporting current
     * aggregate statistics.
     *
     * @return Current values of aggregate statistics
     */
    public StatisticalSummary getSummary() {
        synchronized (statistics) {
            return new StatisticalSummaryValues(getMean(), getVariance(), getN(),
                    getMax(), getMin(), getSum());
        }
    }

    /**
     * Creates and returns a {@code SummaryStatistics} whose data will be
     * aggregated with those of this {@code AggregateSummaryStatistics}.
     *
     * @return a {@code SummaryStatistics} whose data will be aggregated with
     *      those of this {@code AggregateSummaryStatistics}.  The initial state
     *      is a copy of the configured prototype statistics.
     */
    public SummaryStatistics createContributingStatistics() {
        SummaryStatistics contributingStatistics
                = new AggregatingSummaryStatistics(statistics);

        // No try - catch or advertising NAE because neither argument will ever be null
        SummaryStatistics.copy(statisticsPrototype, contributingStatistics);

        return contributingStatistics;
    }

    /**
     * Computes aggregate summary statistics. This method can be used to combine statistics
     * computed over partitions or subsamples - i.e., the StatisticalSummaryValues returned
     * should contain the same values that would have been obtained by computing a single
     * StatisticalSummary over the combined dataset.
     * <p>
     * Returns null if the collection is empty or null.
     * </p>
     *
     * @param statistics collection of SummaryStatistics to aggregate
     * @return summary statistics for the combined dataset
     */
    public static StatisticalSummaryValues aggregate(Collection<? extends StatisticalSummary> statistics) {
        if (statistics == null) {
            return null;
        }
        Iterator<? extends StatisticalSummary> iterator = statistics.iterator();
        if (!iterator.hasNext()) {
            return null;
        }
        StatisticalSummary current = iterator.next();
        long n = current.getN();
        double min = current.getMin();
        double sum = current.getSum();
        double max = current.getMax();
        double var = current.getVariance();
        double m2 = var * (n - 1d);
        double mean = current.getMean();
        while (iterator.hasNext()) {
            current = iterator.next();
            if (current.getMin() < min || Double.isNaN(min)) {
                min = current.getMin();
            }
            if (current.getMax() > max || Double.isNaN(max)) {
                max = current.getMax();
            }
            sum += current.getSum();
            final double oldN = n;
            final double curN = current.getN();
            n += curN;
            final double meanDiff = current.getMean() - mean;
            mean = sum / n;
            final double curM2 = current.getVariance() * (curN - 1d);
            m2 = m2 + curM2 + meanDiff * meanDiff * oldN * curN / n;
        }
        final double variance;
        if (n == 0) {
            variance = Double.NaN;
        } else if (n == 1) {
            variance = 0d;
        } else {
            variance = m2 / (n - 1);
        }
        return new StatisticalSummaryValues(mean, variance, n, max, min, sum);
    }

    /**
     * A SummaryStatistics that also forwards all values added to it to a second
     * {@code SummaryStatistics} for aggregation.
     *
     * @since 2.0
     */
    private static class AggregatingSummaryStatistics extends SummaryStatistics {

        /**
         * The serialization version of this class
         */
        private static final long serialVersionUID = 1L;

        /**
         * An additional SummaryStatistics into which values added to these
         * statistics (and possibly others) are aggregated
         */
        private final SummaryStatistics aggregateStatistics;

        /**
         * Initializes a new AggregatingSummaryStatistics with the specified
         * aggregate statistics object
         *
         * @param aggregateStatistics a {@code SummaryStatistics} into which
         *      values added to this statistics object should be aggregated
         */
        AggregatingSummaryStatistics(SummaryStatistics aggregateStatistics) {
            this.aggregateStatistics = aggregateStatistics;
        }

        /**
         * {@inheritDoc}.  This version adds the provided value to the configured
         * aggregate after adding it to these statistics.
         *
         * @see SummaryStatistics#addValue(double)
         */
        @Override
        public void addValue(double value) {
            super.addValue(value);
            synchronized (aggregateStatistics) {
                aggregateStatistics.addValue(value);
            }
        }

        /**
         * Returns true iff <code>object</code> is a
         * <code>SummaryStatistics</code> instance and all statistics have the
         * same values as this.
         * @param object the object to test equality against.
         * @return true if object equals this
         */
        @Override
        public boolean equals(Object object) {
            if (object == this) {
                return true;
            }
            if (object instanceof AggregatingSummaryStatistics == false) {
                return false;
            }
            AggregatingSummaryStatistics stat = (AggregatingSummaryStatistics)object;
            return super.equals(stat) &&
                   aggregateStatistics.equals(stat.aggregateStatistics);
        }

        /**
         * Returns hash code based on values of statistics
         * @return hash code
         */
        @Override
        public int hashCode() {
            return 123 + super.hashCode() + aggregateStatistics.hashCode();
        }
    }
}
