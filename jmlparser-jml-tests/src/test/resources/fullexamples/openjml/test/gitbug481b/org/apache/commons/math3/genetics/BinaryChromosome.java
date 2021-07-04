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
import org.apache.commons.math3.exception.util.LocalizedFormats;


/**
 * Chromosome represented by a vector of 0s and 1s.
 *
 * @since 2.0
 */
public abstract class BinaryChromosome extends AbstractListChromosome<Integer> {

    /**
     * Constructor.
     * @param representation list of {0,1} values representing the chromosome
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    public BinaryChromosome(List<Integer> representation) throws InvalidRepresentationException {
        super(representation);
    }

    /**
     * Constructor.
     * @param representation array of {0,1} values representing the chromosome
     * @throws InvalidRepresentationException iff the <code>representation</code> can not represent a valid chromosome
     */
    public BinaryChromosome(Integer[] representation) throws InvalidRepresentationException {
        super(representation);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void checkValidity(List<Integer> chromosomeRepresentation) throws InvalidRepresentationException {
        for (int i : chromosomeRepresentation) {
            if (i < 0 || i >1) {
                throw new InvalidRepresentationException(LocalizedFormats.INVALID_BINARY_DIGIT,
                                                         i);
            }
        }
    }

    /**
     * Returns a representation of a random binary array of length <code>length</code>.
     * @param length length of the array
     * @return a random binary array of length <code>length</code>
     */
    public static List<Integer> randomBinaryRepresentation(int length) {
        // random binary list
        List<Integer> rList= new ArrayList<Integer> (length);
        for (int j=0; j<length; j++) {
            rList.add(GeneticAlgorithm.getRandomGenerator().nextInt(2));
        }
        return rList;
    }

    /** {@inheritDoc} */
    @Override
    protected boolean isSame(Chromosome another) {
        // type check
        if (! (another instanceof BinaryChromosome)) {
            return false;
        }
        BinaryChromosome anotherBc = (BinaryChromosome) another;
        // size check
        if (getLength() != anotherBc.getLength()) {
            return false;
        }

        for (int i=0; i< getRepresentation().size(); i++) {
            if (!(getRepresentation().get(i).equals(anotherBc.getRepresentation().get(i)))) {
                return false;
            }
        }
        // all is ok
        return true;
    }
}
