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

package org.apache.commons.math3.stat.ranking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.exception.NotANumberException;
import org.apache.commons.math3.random.RandomDataGenerator;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.util.FastMath;


/**
 * <p> Ranking based on the natural ordering on doubles.</p>
 * <p>NaNs are treated according to the configured {@link NaNStrategy} and ties
 * are handled using the selected {@link TiesStrategy}.
 * Configuration settings are supplied in optional constructor arguments.
 * Defaults are {@link NaNStrategy#FAILED} and {@link TiesStrategy#AVERAGE},
 * respectively. When using {@link TiesStrategy#RANDOM}, a
 * {@link RandomGenerator} may be supplied as a constructor argument.</p>
 * <p>Examples:
 * <table border="1" cellpadding="3">
 * <tr><th colspan="3">
 * Input data: (20, 17, 30, 42.3, 17, 50, Double.NaN, Double.NEGATIVE_INFINITY, 17)
 * </th></tr>
 * <tr><th>NaNStrategy</th><th>TiesStrategy</th>
 * <th><code>rank(data)</code></th>
 * <tr>
 * <td>default (NaNs maximal)</td>
 * <td>default (ties averaged)</td>
 * <td>(5, 3, 6, 7, 3, 8, 9, 1, 3)</td></tr>
 * <tr>
 * <td>default (NaNs maximal)</td>
 * <td>MINIMUM</td>
 * <td>(5, 2, 6, 7, 2, 8, 9, 1, 2)</td></tr>
 * <tr>
 * <td>MINIMAL</td>
 * <td>default (ties averaged)</td>
 * <td>(6, 4, 7, 8, 4, 9, 1.5, 1.5, 4)</td></tr>
 * <tr>
 * <td>REMOVED</td>
 * <td>SEQUENTIAL</td>
 * <td>(5, 2, 6, 7, 3, 8, 1, 4)</td></tr>
 * <tr>
 * <td>MINIMAL</td>
 * <td>MAXIMUM</td>
 * <td>(6, 5, 7, 8, 5, 9, 2, 2, 5)</td></tr></table></p>
 *
 * @since 2.0
 */
public class NaturalRanking implements RankingAlgorithm {

    /** default NaN strategy */
    public static final NaNStrategy DEFAULT_NAN_STRATEGY = NaNStrategy.FAILED;

    /** default ties strategy */
    public static final TiesStrategy DEFAULT_TIES_STRATEGY = TiesStrategy.AVERAGE;

    /** NaN strategy - defaults to NaNs maximal */
    private final NaNStrategy nanStrategy;

    /** Ties strategy - defaults to ties averaged */
    private final TiesStrategy tiesStrategy;

    /** Source of random data - used only when ties strategy is RANDOM */
    private final RandomDataGenerator randomData;

    /**
     * Create a NaturalRanking with default strategies for handling ties and NaNs.
     */
    public NaturalRanking() {
        super();
        tiesStrategy = DEFAULT_TIES_STRATEGY;
        nanStrategy = DEFAULT_NAN_STRATEGY;
        randomData = null;
    }

    /**
     * Create a NaturalRanking with the given TiesStrategy.
     *
     * @param tiesStrategy the TiesStrategy to use
     */
    public NaturalRanking(TiesStrategy tiesStrategy) {
        super();
        this.tiesStrategy = tiesStrategy;
        nanStrategy = DEFAULT_NAN_STRATEGY;
        randomData = new RandomDataGenerator();
    }

    /**
     * Create a NaturalRanking with the given NaNStrategy.
     *
     * @param nanStrategy the NaNStrategy to use
     */
    public NaturalRanking(NaNStrategy nanStrategy) {
        super();
        this.nanStrategy = nanStrategy;
        tiesStrategy = DEFAULT_TIES_STRATEGY;
        randomData = null;
    }

    /**
     * Create a NaturalRanking with the given NaNStrategy and TiesStrategy.
     *
     * @param nanStrategy NaNStrategy to use
     * @param tiesStrategy TiesStrategy to use
     */
    public NaturalRanking(NaNStrategy nanStrategy, TiesStrategy tiesStrategy) {
        super();
        this.nanStrategy = nanStrategy;
        this.tiesStrategy = tiesStrategy;
        randomData = new RandomDataGenerator();
    }

    /**
     * Create a NaturalRanking with TiesStrategy.RANDOM and the given
     * RandomGenerator as the source of random data.
     *
     * @param randomGenerator source of random data
     */
    public NaturalRanking(RandomGenerator randomGenerator) {
        super();
        this.tiesStrategy = TiesStrategy.RANDOM;
        nanStrategy = DEFAULT_NAN_STRATEGY;
        randomData = new RandomDataGenerator(randomGenerator);
    }


    /**
     * Create a NaturalRanking with the given NaNStrategy, TiesStrategy.RANDOM
     * and the given source of random data.
     *
     * @param nanStrategy NaNStrategy to use
     * @param randomGenerator source of random data
     */
    public NaturalRanking(NaNStrategy nanStrategy,
            RandomGenerator randomGenerator) {
        super();
        this.nanStrategy = nanStrategy;
        this.tiesStrategy = TiesStrategy.RANDOM;
        randomData = new RandomDataGenerator(randomGenerator);
    }

    /**
     * Return the NaNStrategy
     *
     * @return returns the NaNStrategy
     */
    public NaNStrategy getNanStrategy() {
        return nanStrategy;
    }

    /**
     * Return the TiesStrategy
     *
     * @return the TiesStrategy
     */
    public TiesStrategy getTiesStrategy() {
        return tiesStrategy;
    }

    /**
     * Rank <code>data</code> using the natural ordering on Doubles, with
     * NaN values handled according to <code>nanStrategy</code> and ties
     * resolved using <code>tiesStrategy.</code>
     *
     * @param data array to be ranked
     * @return array of ranks
     * @throws NotANumberException if the selected {@link NaNStrategy} is {@code FAILED}
     * and a {@link Double#NaN} is encountered in the input data
     */
    public double[] rank(double[] data) {

        // Array recording initial positions of data to be ranked
        IntDoublePair[] ranks = new IntDoublePair[data.length];
        for (int i = 0; i < data.length; i++) {
            ranks[i] = new IntDoublePair(data[i], i);
        }

        // Recode, remove or record positions of NaNs
        List<Integer> nanPositions = null;
        switch (nanStrategy) {
            case MAXIMAL: // Replace NaNs with +INFs
                recodeNaNs(ranks, Double.POSITIVE_INFINITY);
                break;
            case MINIMAL: // Replace NaNs with -INFs
                recodeNaNs(ranks, Double.NEGATIVE_INFINITY);
                break;
            case REMOVED: // Drop NaNs from data
                ranks = removeNaNs(ranks);
                break;
            case FIXED:   // Record positions of NaNs
                nanPositions = getNanPositions(ranks);
                break;
            case FAILED:
                nanPositions = getNanPositions(ranks);
                if (nanPositions.size() > 0) {
                    throw new NotANumberException();
                }
                break;
            default: // this should not happen unless NaNStrategy enum is changed
                throw new MathInternalError();
        }

        // Sort the IntDoublePairs
        Arrays.sort(ranks);

        // Walk the sorted array, filling output array using sorted positions,
        // resolving ties as we go
        double[] out = new double[ranks.length];
        int pos = 1;  // position in sorted array
        out[ranks[0].getPosition()] = pos;
        List<Integer> tiesTrace = new ArrayList<Integer>();
        tiesTrace.add(ranks[0].getPosition());
        for (int i = 1; i < ranks.length; i++) {
            if (Double.compare(ranks[i].getValue(), ranks[i - 1].getValue()) > 0) {
                // tie sequence has ended (or had length 1)
                pos = i + 1;
                if (tiesTrace.size() > 1) {  // if seq is nontrivial, resolve
                    resolveTie(out, tiesTrace);
                }
                tiesTrace = new ArrayList<Integer>();
                tiesTrace.add(ranks[i].getPosition());
            } else {
                // tie sequence continues
                tiesTrace.add(ranks[i].getPosition());
            }
            out[ranks[i].getPosition()] = pos;
        }
        if (tiesTrace.size() > 1) {  // handle tie sequence at end
            resolveTie(out, tiesTrace);
        }
        if (nanStrategy == NaNStrategy.FIXED) {
            restoreNaNs(out, nanPositions);
        }
        return out;
    }

    /**
     * Returns an array that is a copy of the input array with IntDoublePairs
     * having NaN values removed.
     *
     * @param ranks input array
     * @return array with NaN-valued entries removed
     */
    private IntDoublePair[] removeNaNs(IntDoublePair[] ranks) {
        if (!containsNaNs(ranks)) {
            return ranks;
        }
        IntDoublePair[] outRanks = new IntDoublePair[ranks.length];
        int j = 0;
        for (int i = 0; i < ranks.length; i++) {
            if (Double.isNaN(ranks[i].getValue())) {
                // drop, but adjust original ranks of later elements
                for (int k = i + 1; k < ranks.length; k++) {
                    ranks[k] = new IntDoublePair(
                            ranks[k].getValue(), ranks[k].getPosition() - 1);
                }
            } else {
                outRanks[j] = new IntDoublePair(
                        ranks[i].getValue(), ranks[i].getPosition());
                j++;
            }
        }
        IntDoublePair[] returnRanks = new IntDoublePair[j];
        System.arraycopy(outRanks, 0, returnRanks, 0, j);
        return returnRanks;
    }

    /**
     * Recodes NaN values to the given value.
     *
     * @param ranks array to recode
     * @param value the value to replace NaNs with
     */
    private void recodeNaNs(IntDoublePair[] ranks, double value) {
        for (int i = 0; i < ranks.length; i++) {
            if (Double.isNaN(ranks[i].getValue())) {
                ranks[i] = new IntDoublePair(
                        value, ranks[i].getPosition());
            }
        }
    }

    /**
     * Checks for presence of NaNs in <code>ranks.</code>
     *
     * @param ranks array to be searched for NaNs
     * @return true iff ranks contains one or more NaNs
     */
    private boolean containsNaNs(IntDoublePair[] ranks) {
        for (int i = 0; i < ranks.length; i++) {
            if (Double.isNaN(ranks[i].getValue())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Resolve a sequence of ties, using the configured {@link TiesStrategy}.
     * The input <code>ranks</code> array is expected to take the same value
     * for all indices in <code>tiesTrace</code>.  The common value is recoded
     * according to the tiesStrategy. For example, if ranks = <5,8,2,6,2,7,1,2>,
     * tiesTrace = <2,4,7> and tiesStrategy is MINIMUM, ranks will be unchanged.
     * The same array and trace with tiesStrategy AVERAGE will come out
     * <5,8,3,6,3,7,1,3>.
     *
     * @param ranks array of ranks
     * @param tiesTrace list of indices where <code>ranks</code> is constant
     * -- that is, for any i and j in TiesTrace, <code> ranks[i] == ranks[j]
     * </code>
     */
    private void resolveTie(double[] ranks, List<Integer> tiesTrace) {

        // constant value of ranks over tiesTrace
        final double c = ranks[tiesTrace.get(0)];

        // length of sequence of tied ranks
        final int length = tiesTrace.size();

        switch (tiesStrategy) {
            case  AVERAGE:  // Replace ranks with average
                fill(ranks, tiesTrace, (2 * c + length - 1) / 2d);
                break;
            case MAXIMUM:   // Replace ranks with maximum values
                fill(ranks, tiesTrace, c + length - 1);
                break;
            case MINIMUM:   // Replace ties with minimum
                fill(ranks, tiesTrace, c);
                break;
            case RANDOM:    // Fill with random integral values in [c, c + length - 1]
                Iterator<Integer> iterator = tiesTrace.iterator();
                long f = FastMath.round(c);
                while (iterator.hasNext()) {
                    // No advertised exception because args are guaranteed valid
                    ranks[iterator.next()] =
                        randomData.nextLong(f, f + length - 1);
                }
                break;
            case SEQUENTIAL:  // Fill sequentially from c to c + length - 1
                // walk and fill
                iterator = tiesTrace.iterator();
                f = FastMath.round(c);
                int i = 0;
                while (iterator.hasNext()) {
                    ranks[iterator.next()] = f + i++;
                }
                break;
            default: // this should not happen unless TiesStrategy enum is changed
                throw new MathInternalError();
        }
    }

    /**
     * Sets<code>data[i] = value</code> for each i in <code>tiesTrace.</code>
     *
     * @param data array to modify
     * @param tiesTrace list of index values to set
     * @param value value to set
     */
    private void fill(double[] data, List<Integer> tiesTrace, double value) {
        Iterator<Integer> iterator = tiesTrace.iterator();
        while (iterator.hasNext()) {
            data[iterator.next()] = value;
        }
    }

    /**
     * Set <code>ranks[i] = Double.NaN</code> for each i in <code>nanPositions.</code>
     *
     * @param ranks array to modify
     * @param nanPositions list of index values to set to <code>Double.NaN</code>
     */
    private void restoreNaNs(double[] ranks, List<Integer> nanPositions) {
        if (nanPositions.size() == 0) {
            return;
        }
        Iterator<Integer> iterator = nanPositions.iterator();
        while (iterator.hasNext()) {
            ranks[iterator.next().intValue()] = Double.NaN;
        }

    }

    /**
     * Returns a list of indexes where <code>ranks</code> is <code>NaN.</code>
     *
     * @param ranks array to search for <code>NaNs</code>
     * @return list of indexes i such that <code>ranks[i] = NaN</code>
     */
    private List<Integer> getNanPositions(IntDoublePair[] ranks) {
        ArrayList<Integer> out = new ArrayList<Integer>();
        for (int i = 0; i < ranks.length; i++) {
            if (Double.isNaN(ranks[i].getValue())) {
                out.add(Integer.valueOf(i));
            }
        }
        return out;
    }

    /**
     * Represents the position of a double value in an ordering.
     * Comparable interface is implemented so Arrays.sort can be used
     * to sort an array of IntDoublePairs by value.  Note that the
     * implicitly defined natural ordering is NOT consistent with equals.
     */
    private static class IntDoublePair implements Comparable<IntDoublePair>  {

        /** Value of the pair */
        private final double value;

        /** Original position of the pair */
        private final int position;

        /**
         * Construct an IntDoublePair with the given value and position.
         * @param value the value of the pair
         * @param position the original position
         */
        IntDoublePair(double value, int position) {
            this.value = value;
            this.position = position;
        }

        /**
         * Compare this IntDoublePair to another pair.
         * Only the <strong>values</strong> are compared.
         *
         * @param other the other pair to compare this to
         * @return result of <code>Double.compare(value, other.value)</code>
         */
        public int compareTo(IntDoublePair other) {
            return Double.compare(value, other.value);
        }

        // N.B. equals() and hashCode() are not implemented; see MATH-610 for discussion.

        /**
         * Returns the value of the pair.
         * @return value
         */
        public double getValue() {
            return value;
        }

        /**
         * Returns the original position of the pair.
         * @return position
         */
        public int getPosition() {
            return position;
        }
    }
}
