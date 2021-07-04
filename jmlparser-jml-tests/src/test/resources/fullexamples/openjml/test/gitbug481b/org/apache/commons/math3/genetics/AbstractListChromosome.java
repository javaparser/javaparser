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
import java.util.List;

/**
 * Chromosome represented by an immutable list of a fixed length.
 *
 * @param <T> type of the representation list
 * @since 2.0
 */
public abstract class AbstractListChromosome<T> extends Chromosome {

    /** List representing the chromosome */
    private final List<T> representation;

    /**
     * Constructor, copying the input representation.
     * @param representation inner representation of the chromosome
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    public AbstractListChromosome(final List<T> representation) throws InvalidRepresentationException {
        this(representation, true);
    }

    /**
     * Constructor, copying the input representation.
     * @param representation inner representation of the chromosome
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    public AbstractListChromosome(final T[] representation) throws InvalidRepresentationException {
        this(Arrays.asList(representation));
    }

    /**
     * Constructor.
     * @param representation inner representation of the chromosome
     * @param copyList if {@code true}, the representation will be copied, otherwise it will be referenced.
     * @since 3.3
     */
    public AbstractListChromosome(final List<T> representation, final boolean copyList) {
        checkValidity(representation);
        this.representation =
                Collections.unmodifiableList(copyList ? new ArrayList<T>(representation) : representation);
    }

    /**
     * Asserts that <code>representation</code> can represent a valid chromosome.
     *
     * @param chromosomeRepresentation representation of the chromosome
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    protected abstract void checkValidity(List<T> chromosomeRepresentation) throws InvalidRepresentationException;

    /**
     * Returns the (immutable) inner representation of the chromosome.
     * @return the representation of the chromosome
     */
    protected List<T> getRepresentation() {
        return representation;
    }

    /**
     * Returns the length of the chromosome.
     * @return the length of the chromosome
     */
    public int getLength() {
        return getRepresentation().size();
    }

    /**
     * Creates a new instance of the same class as <code>this</code> is, with a given <code>arrayRepresentation</code>.
     * This is needed in crossover and mutation operators, where we need a new instance of the same class, but with
     * different array representation.
     * <p>
     * Usually, this method just calls a constructor of the class.
     *
     * @param chromosomeRepresentation the inner array representation of the new chromosome.
     * @return new instance extended from FixedLengthChromosome with the given arrayRepresentation
     */
    public abstract AbstractListChromosome<T> newFixedLengthChromosome(final List<T> chromosomeRepresentation);

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("(f=%s %s)", getFitness(), getRepresentation());
    }
}
