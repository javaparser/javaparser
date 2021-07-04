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
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;

/**
 * Population of chromosomes represented by a {@link List}.
 *
 * @since 2.0
 */
public abstract class ListPopulation implements Population {

    /** List of chromosomes */
    private List<Chromosome> chromosomes;

    /** maximal size of the population */
    private int populationLimit;

    /**
     * Creates a new ListPopulation instance and initializes its inner chromosome list.
     *
     * @param populationLimit maximal size of the population
     * @throws NotPositiveException if the population limit is not a positive number (&lt; 1)
     */
    public ListPopulation(final int populationLimit) throws NotPositiveException {
        this(Collections.<Chromosome> emptyList(), populationLimit);
    }

    /**
     * Creates a new ListPopulation instance.
     * <p>
     * Note: the chromosomes of the specified list are added to the population.
     *
     * @param chromosomes list of chromosomes to be added to the population
     * @param populationLimit maximal size of the population
     * @throws NullArgumentException if the list of chromosomes is {@code null}
     * @throws NotPositiveException if the population limit is not a positive number (&lt; 1)
     * @throws NumberIsTooLargeException if the list of chromosomes exceeds the population limit
     */
    public ListPopulation(final List<Chromosome> chromosomes, final int populationLimit)
        throws NullArgumentException, NotPositiveException, NumberIsTooLargeException {

        if (chromosomes == null) {
            throw new NullArgumentException();
        }
        if (populationLimit <= 0) {
            throw new NotPositiveException(LocalizedFormats.POPULATION_LIMIT_NOT_POSITIVE, populationLimit);
        }
        if (chromosomes.size() > populationLimit) {
            throw new NumberIsTooLargeException(LocalizedFormats.LIST_OF_CHROMOSOMES_BIGGER_THAN_POPULATION_SIZE,
                                                chromosomes.size(), populationLimit, false);
        }
        this.populationLimit = populationLimit;
        this.chromosomes = new ArrayList<Chromosome>(populationLimit);
        this.chromosomes.addAll(chromosomes);
    }

    /**
     * Sets the list of chromosomes.
     * <p>
     * Note: this method removes all existing chromosomes in the population and adds all chromosomes
     * of the specified list to the population.
     *
     * @param chromosomes the list of chromosomes
     * @throws NullArgumentException if the list of chromosomes is {@code null}
     * @throws NumberIsTooLargeException if the list of chromosomes exceeds the population limit
     * @deprecated use {@link #addChromosomes(Collection)} instead
     */
    @Deprecated
    public void setChromosomes(final List<Chromosome> chromosomes)
        throws NullArgumentException, NumberIsTooLargeException {

        if (chromosomes == null) {
            throw new NullArgumentException();
        }
        if (chromosomes.size() > populationLimit) {
            throw new NumberIsTooLargeException(LocalizedFormats.LIST_OF_CHROMOSOMES_BIGGER_THAN_POPULATION_SIZE,
                                                chromosomes.size(), populationLimit, false);
        }
        this.chromosomes.clear();
        this.chromosomes.addAll(chromosomes);
    }

    /**
     * Add a {@link Collection} of chromosomes to this {@link Population}.
     * @param chromosomeColl a {@link Collection} of chromosomes
     * @throws NumberIsTooLargeException if the population would exceed the population limit when
     * adding this chromosome
     * @since 3.1
     */
    public void addChromosomes(final Collection<Chromosome> chromosomeColl) throws NumberIsTooLargeException {
        if (chromosomes.size() + chromosomeColl.size() > populationLimit) {
            throw new NumberIsTooLargeException(LocalizedFormats.LIST_OF_CHROMOSOMES_BIGGER_THAN_POPULATION_SIZE,
                                                chromosomes.size(), populationLimit, false);
        }
        this.chromosomes.addAll(chromosomeColl);
    }

    /**
     * Returns an unmodifiable list of the chromosomes in this population.
     * @return the unmodifiable list of chromosomes
     */
    public List<Chromosome> getChromosomes() {
        return Collections.unmodifiableList(chromosomes);
    }

    /**
     * Access the list of chromosomes.
     * @return the list of chromosomes
     * @since 3.1
     */
    protected List<Chromosome> getChromosomeList() {
        return chromosomes;
    }

    /**
     * Add the given chromosome to the population.
     *
     * @param chromosome the chromosome to add.
     * @throws NumberIsTooLargeException if the population would exceed the {@code populationLimit} after
     *   adding this chromosome
     */
    public void addChromosome(final Chromosome chromosome) throws NumberIsTooLargeException {
        if (chromosomes.size() >= populationLimit) {
            throw new NumberIsTooLargeException(LocalizedFormats.LIST_OF_CHROMOSOMES_BIGGER_THAN_POPULATION_SIZE,
                                                chromosomes.size(), populationLimit, false);
        }
        this.chromosomes.add(chromosome);
    }

    /**
     * Access the fittest chromosome in this population.
     * @return the fittest chromosome.
     */
    public Chromosome getFittestChromosome() {
        // best so far
        Chromosome bestChromosome = this.chromosomes.get(0);
        for (Chromosome chromosome : this.chromosomes) {
            if (chromosome.compareTo(bestChromosome) > 0) {
                // better chromosome found
                bestChromosome = chromosome;
            }
        }
        return bestChromosome;
    }

    /**
     * Access the maximum population size.
     * @return the maximum population size.
     */
    public int getPopulationLimit() {
        return this.populationLimit;
    }

    /**
     * Sets the maximal population size.
     * @param populationLimit maximal population size.
     * @throws NotPositiveException if the population limit is not a positive number (&lt; 1)
     * @throws NumberIsTooSmallException if the new population size is smaller than the current number
     *   of chromosomes in the population
     */
    public void setPopulationLimit(final int populationLimit) throws NotPositiveException, NumberIsTooSmallException {
        if (populationLimit <= 0) {
            throw new NotPositiveException(LocalizedFormats.POPULATION_LIMIT_NOT_POSITIVE, populationLimit);
        }
        if (populationLimit < chromosomes.size()) {
            throw new NumberIsTooSmallException(populationLimit, chromosomes.size(), true);
        }
        this.populationLimit = populationLimit;
    }

    /**
     * Access the current population size.
     * @return the current population size.
     */
    public int getPopulationSize() {
        return this.chromosomes.size();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.chromosomes.toString();
    }

    /**
     * Returns an iterator over the unmodifiable list of chromosomes.
     * <p>Any call to {@link Iterator#remove()} will result in a {@link UnsupportedOperationException}.</p>
     *
     * @return chromosome iterator
     */
    public Iterator<Chromosome> iterator() {
        return getChromosomes().iterator();
    }
}
