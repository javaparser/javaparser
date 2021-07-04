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
import java.util.List;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Tournament selection scheme. Each of the two selected chromosomes is selected
 * based on n-ary tournament -- this is done by drawing {@link #arity} random
 * chromosomes without replacement from the population, and then selecting the
 * fittest chromosome among them.
 *
 * @since 2.0
 */
public class TournamentSelection implements SelectionPolicy {

    /** number of chromosomes included in the tournament selections */
    private int arity;

    /**
     * Creates a new TournamentSelection instance.
     *
     * @param arity how many chromosomes will be drawn to the tournament
     */
    public TournamentSelection(final int arity) {
        this.arity = arity;
    }

    /**
     * Select two chromosomes from the population. Each of the two selected
     * chromosomes is selected based on n-ary tournament -- this is done by
     * drawing {@link #arity} random chromosomes without replacement from the
     * population, and then selecting the fittest chromosome among them.
     *
     * @param population the population from which the chromosomes are chosen.
     * @return the selected chromosomes.
     * @throws MathIllegalArgumentException if the tournament arity is bigger than the population size
     */
    public ChromosomePair select(final Population population) throws MathIllegalArgumentException {
        return new ChromosomePair(tournament((ListPopulation) population),
                                  tournament((ListPopulation) population));
    }

    /**
     * Helper for {@link #select(Population)}. Draw {@link #arity} random chromosomes without replacement from the
     * population, and then select the fittest chromosome among them.
     *
     * @param population the population from which the chromosomes are chosen.
     * @return the selected chromosome.
     * @throws MathIllegalArgumentException if the tournament arity is bigger than the population size
     */
    private Chromosome tournament(final ListPopulation population) throws MathIllegalArgumentException {
        if (population.getPopulationSize() < this.arity) {
            throw new MathIllegalArgumentException(LocalizedFormats.TOO_LARGE_TOURNAMENT_ARITY,
                                                   arity, population.getPopulationSize());
        }
        // auxiliary population
        ListPopulation tournamentPopulation = new ListPopulation(this.arity) {
            /** {@inheritDoc} */
            public Population nextGeneration() {
                // not useful here
                return null;
            }
        };

        // create a copy of the chromosome list
        List<Chromosome> chromosomes = new ArrayList<Chromosome> (population.getChromosomes());
        for (int i=0; i<this.arity; i++) {
            // select a random individual and add it to the tournament
            int rind = GeneticAlgorithm.getRandomGenerator().nextInt(chromosomes.size());
            tournamentPopulation.addChromosome(chromosomes.get(rind));
            // do not select it again
            chromosomes.remove(rind);
        }
        // the winner takes it all
        return tournamentPopulation.getFittestChromosome();
    }

    /**
     * Gets the arity (number of chromosomes drawn to the tournament).
     *
     * @return arity of the tournament
     */
    public int getArity() {
        return arity;
    }

    /**
     * Sets the arity (number of chromosomes drawn to the tournament).
     *
     * @param arity arity of the tournament
     */
    public void setArity(final int arity) {
        this.arity = arity;
    }

}
