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
package org.apache.commons.math3.genetics;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Random Key chromosome is used for permutation representation. It is a vector
 * of a fixed length of real numbers in [0,1] interval. The index of the i-th
 * smallest value in the vector represents an i-th member of the permutation.
 * <p>
 * For example, the random key [0.2, 0.3, 0.8, 0.1] corresponds to the
 * permutation of indices (3,0,1,2). If the original (unpermuted) sequence would
 * be (a,b,c,d), this would mean the sequence (d,a,b,c).
 * <p>
 * With this representation, common operators like n-point crossover can be
 * used, because any such chromosome represents a valid permutation.
 * <p>
 * Since the chromosome (and thus its arrayRepresentation) is immutable, the
 * array representation is sorted only once in the constructor.
 * <p>
 * For details, see:
 * <ul>
 *   <li>Bean, J.C.: Genetic algorithms and random keys for sequencing and
 *       optimization. ORSA Journal on Computing 6 (1994) 154-160</li>
 *   <li>Rothlauf, F.: Representations for Genetic and Evolutionary Algorithms.
 *       Volume 104 of Studies in Fuzziness and Soft Computing. Physica-Verlag,
 *       Heidelberg (2002)</li>
 * </ul>
 *
 * @param <T> type of the permuted objects
 * @since 2.0
 */
public abstract class RandomKey<T> extends AbstractListChromosome<Double> implements PermutationChromosome<T> {

    /** Cache of sorted representation (unmodifiable). */
    private final List<Double> sortedRepresentation;

    /**
     * Base sequence [0,1,...,n-1], permuted according to the representation (unmodifiable).
     */
    private final List<Integer> baseSeqPermutation;

    /**
     * Constructor.
     *
     * @param representation list of [0,1] values representing the permutation
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    public RandomKey(final List<Double> representation) throws InvalidRepresentationException {
        super(representation);
        // store the sorted representation
        List<Double> sortedRepr = new ArrayList<Double> (getRepresentation());
        Collections.sort(sortedRepr);
        sortedRepresentation = Collections.unmodifiableList(sortedRepr);
        // store the permutation of [0,1,...,n-1] list for toString() and isSame() methods
        baseSeqPermutation = Collections.unmodifiableList(
            decodeGeneric(baseSequence(getLength()), getRepresentation(), sortedRepresentation)
        );
    }

    /**
     * Constructor.
     *
     * @param representation array of [0,1] values representing the permutation
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    public RandomKey(final Double[] representation) throws InvalidRepresentationException {
        this(Arrays.asList(representation));
    }

    /**
     * {@inheritDoc}
     */
    public List<T> decode(final List<T> sequence) {
        return decodeGeneric(sequence, getRepresentation(), sortedRepresentation);
    }

    /**
     * Decodes a permutation represented by <code>representation</code> and
     * returns a (generic) list with the permuted values.
     *
     * @param <S> generic type of the sequence values
     * @param sequence the unpermuted sequence
     * @param representation representation of the permutation ([0,1] vector)
     * @param sortedRepr sorted <code>representation</code>
     * @return list with the sequence values permuted according to the representation
     * @throws DimensionMismatchException iff the length of the <code>sequence</code>,
     *   <code>representation</code> or <code>sortedRepr</code> lists are not equal
     */
    private static <S> List<S> decodeGeneric(final List<S> sequence, List<Double> representation,
                                             final List<Double> sortedRepr)
        throws DimensionMismatchException {

        int l = sequence.size();

        // the size of the three lists must be equal
        if (representation.size() != l) {
            throw new DimensionMismatchException(representation.size(), l);
        }
        if (sortedRepr.size() != l) {
            throw new DimensionMismatchException(sortedRepr.size(), l);
        }

        // do not modify the original representation
        List<Double> reprCopy = new ArrayList<Double> (representation);

        // now find the indices in the original repr and use them for permuting
        List<S> res = new ArrayList<S> (l);
        for (int i=0; i<l; i++) {
            int index = reprCopy.indexOf(sortedRepr.get(i));
            res.add(sequence.get(index));
            reprCopy.set(index, null);
        }
        return res;
    }

    /**
     * Returns <code>true</code> iff <code>another</code> is a RandomKey and
     * encodes the same permutation.
     *
     * @param another chromosome to compare
     * @return true iff chromosomes encode the same permutation
     */
    @Override
    protected boolean isSame(final Chromosome another) {
        // type check
        if (! (another instanceof RandomKey<?>)) {
            return false;
        }
        RandomKey<?> anotherRk = (RandomKey<?>) another;
        // size check
        if (getLength() != anotherRk.getLength()) {
            return false;
        }

        // two different representations can still encode the same permutation
        // the ordering is what counts
        List<Integer> thisPerm = this.baseSeqPermutation;
        List<Integer> anotherPerm = anotherRk.baseSeqPermutation;

        for (int i=0; i<getLength(); i++) {
            if (thisPerm.get(i) != anotherPerm.get(i)) {
                return false;
            }
        }
        // the permutations are the same
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void checkValidity(final List<Double> chromosomeRepresentation)
        throws InvalidRepresentationException {

        for (double val : chromosomeRepresentation) {
            if (val < 0 || val > 1) {
                throw new InvalidRepresentationException(LocalizedFormats.OUT_OF_RANGE_SIMPLE,
                                                         val, 0, 1);
            }
        }
    }


    /**
     * Generates a representation corresponding to a random permutation of
     * length l which can be passed to the RandomKey constructor.
     *
     * @param l length of the permutation
     * @return representation of a random permutation
     */
    public static final List<Double> randomPermutation(final int l) {
        List<Double> repr = new ArrayList<Double>(l);
        for (int i=0; i<l; i++) {
            repr.add(GeneticAlgorithm.getRandomGenerator().nextDouble());
        }
        return repr;
    }

    /**
     * Generates a representation corresponding to an identity permutation of
     * length l which can be passed to the RandomKey constructor.
     *
     * @param l length of the permutation
     * @return representation of an identity permutation
     */
    public static final List<Double> identityPermutation(final int l) {
        List<Double> repr = new ArrayList<Double>(l);
        for (int i=0; i<l; i++) {
            repr.add((double)i/l);
        }
        return repr;
    }

    /**
     * Generates a representation of a permutation corresponding to the
     * <code>data</code> sorted by <code>comparator</code>. The
     * <code>data</code> is not modified during the process.
     *
     * This is useful if you want to inject some permutations to the initial
     * population.
     *
     * @param <S> type of the data
     * @param data list of data determining the order
     * @param comparator how the data will be compared
     * @return list representation of the permutation corresponding to the parameters
     */
    public static <S> List<Double> comparatorPermutation(final List<S> data,
                                                         final Comparator<S> comparator) {
        List<S> sortedData = new ArrayList<S>(data);
        Collections.sort(sortedData, comparator);

        return inducedPermutation(data, sortedData);
    }

    /**
     * Generates a representation of a permutation corresponding to a
     * permutation which yields <code>permutedData</code> when applied to
     * <code>originalData</code>.
     *
     * This method can be viewed as an inverse to {@link #decode(List)}.
     *
     * @param <S> type of the data
     * @param originalData the original, unpermuted data
     * @param permutedData the data, somehow permuted
     * @return representation of a permutation corresponding to the permutation
     *   <code>originalData -> permutedData</code>
     * @throws DimensionMismatchException iff the length of <code>originalData</code>
     *   and <code>permutedData</code> lists are not equal
     * @throws MathIllegalArgumentException iff the <code>permutedData</code> and
     *   <code>originalData</code> lists contain different data
     */
    public static <S> List<Double> inducedPermutation(final List<S> originalData,
                                                      final List<S> permutedData)
        throws DimensionMismatchException, MathIllegalArgumentException {

        if (originalData.size() != permutedData.size()) {
            throw new DimensionMismatchException(permutedData.size(), originalData.size());
        }
        int l = originalData.size();

        List<S> origDataCopy = new ArrayList<S> (originalData);

        Double[] res = new Double[l];
        for (int i=0; i<l; i++) {
            int index = origDataCopy.indexOf(permutedData.get(i));
            if (index == -1) {
                throw new MathIllegalArgumentException(LocalizedFormats.DIFFERENT_ORIG_AND_PERMUTED_DATA);
            }
            res[index] = (double) i / l;
            origDataCopy.set(index, null);
        }
        return Arrays.asList(res);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("(f=%s pi=(%s))", getFitness(), baseSeqPermutation);
    }

    /**
     * Helper for constructor. Generates a list of natural numbers (0,1,...,l-1).
     *
     * @param l length of list to generate
     * @return list of integers from 0 to l-1
     */
    private static List<Integer> baseSequence(final int l) {
        List<Integer> baseSequence = new ArrayList<Integer> (l);
        for (int i=0; i<l; i++) {
            baseSequence.add(i);
        }
        return baseSequence;
    }
}
