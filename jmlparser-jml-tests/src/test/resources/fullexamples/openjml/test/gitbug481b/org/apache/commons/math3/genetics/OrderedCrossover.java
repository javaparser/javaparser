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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.util.FastMath;

/**
 * Order 1 Crossover [OX1] builds offspring from <b>ordered</b> chromosomes by copying a
 * consecutive slice from one parent, and filling up the remaining genes from the other
 * parent as they appear.
 * <p>
 * This policy works by applying the following rules:
 * <ol>
 *   <li>select a random slice of consecutive genes from parent 1</li>
 *   <li>copy the slice to child 1 and mark out the genes in parent 2</li>
 *   <li>starting from the right side of the slice, copy genes from parent 2 as they
 *       appear to child 1 if they are not yet marked out.</li>
 * </ol>
 * <p>
 * Example (random sublist from index 3 to 7, underlined):
 * <pre>
 * p1 = (8 4 7 3 6 2 5 1 9 0)   X   c1 = (0 4 7 3 6 2 5 1 8 9)
 *             ---------                        ---------
 * p2 = (0 1 2 3 4 5 6 7 8 9)   X   c2 = (8 1 2 3 4 5 6 7 9 0)
 * </pre>
 * <p>
 * This policy works only on {@link AbstractListChromosome}, and therefore it
 * is parameterized by T. Moreover, the chromosomes must have same lengths.
 *
 * @see <a href="http://www.rubicite.com/Tutorials/GeneticAlgorithms/CrossoverOperators/Order1CrossoverOperator.aspx">
 * Order 1 Crossover Operator</a>
 *
 * @param <T> generic type of the {@link AbstractListChromosome}s for crossover
 * @since 3.1
 */
public class OrderedCrossover<T> implements CrossoverPolicy {

    /**
     * {@inheritDoc}
     *
     * @throws MathIllegalArgumentException iff one of the chromosomes is
     *   not an instance of {@link AbstractListChromosome}
     * @throws DimensionMismatchException if the length of the two chromosomes is different
     */
    @SuppressWarnings("unchecked")
    public ChromosomePair crossover(final Chromosome first, final Chromosome second)
        throws DimensionMismatchException, MathIllegalArgumentException {

        if (!(first instanceof AbstractListChromosome<?> && second instanceof AbstractListChromosome<?>)) {
            throw new MathIllegalArgumentException(LocalizedFormats.INVALID_FIXED_LENGTH_CHROMOSOME);
        }
        return mate((AbstractListChromosome<T>) first, (AbstractListChromosome<T>) second);
    }

    /**
     * Helper for {@link #crossover(Chromosome, Chromosome)}. Performs the actual crossover.
     *
     * @param first the first chromosome
     * @param second the second chromosome
     * @return the pair of new chromosomes that resulted from the crossover
     * @throws DimensionMismatchException if the length of the two chromosomes is different
     */
    protected ChromosomePair mate(final AbstractListChromosome<T> first, final AbstractListChromosome<T> second)
        throws DimensionMismatchException {

        final int length = first.getLength();
        if (length != second.getLength()) {
            throw new DimensionMismatchException(second.getLength(), length);
        }

        // array representations of the parents
        final List<T> parent1Rep = first.getRepresentation();
        final List<T> parent2Rep = second.getRepresentation();
        // and of the children
        final List<T> child1 = new ArrayList<T>(length);
        final List<T> child2 = new ArrayList<T>(length);
        // sets of already inserted items for quick access
        final Set<T> child1Set = new HashSet<T>(length);
        final Set<T> child2Set = new HashSet<T>(length);

        final RandomGenerator random = GeneticAlgorithm.getRandomGenerator();
        // choose random points, making sure that lb < ub.
        int a = random.nextInt(length);
        int b;
        do {
            b = random.nextInt(length);
        } while (a == b);
        // determine the lower and upper bounds
        final int lb = FastMath.min(a, b);
        final int ub = FastMath.max(a, b);

        // add the subLists that are between lb and ub
        child1.addAll(parent1Rep.subList(lb, ub + 1));
        child1Set.addAll(child1);
        child2.addAll(parent2Rep.subList(lb, ub + 1));
        child2Set.addAll(child2);

        // iterate over every item in the parents
        for (int i = 1; i <= length; i++) {
            final int idx = (ub + i) % length;

            // retrieve the current item in each parent
            final T item1 = parent1Rep.get(idx);
            final T item2 = parent2Rep.get(idx);

            // if the first child already contains the item in the second parent add it
            if (!child1Set.contains(item2)) {
                child1.add(item2);
                child1Set.add(item2);
            }

            // if the second child already contains the item in the first parent add it
            if (!child2Set.contains(item1)) {
                child2.add(item1);
                child2Set.add(item1);
            }
        }

        // rotate so that the original slice is in the same place as in the parents.
        Collections.rotate(child1, lb);
        Collections.rotate(child2, lb);

        return new ChromosomePair(first.newFixedLengthChromosome(child1),
                                  second.newFixedLengthChromosome(child2));
    }
}
