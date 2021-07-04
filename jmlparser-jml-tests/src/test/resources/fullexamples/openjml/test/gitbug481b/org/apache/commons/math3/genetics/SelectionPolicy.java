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

import org.apache.commons.math3.exception.MathIllegalArgumentException;

/**
 * Algorithm used to select a chromosome pair from a population.
 *
 * @since 2.0
 */
public interface SelectionPolicy {
    /**
     * Select two chromosomes from the population.
     * @param population the population from which the chromosomes are choosen.
     * @return the selected chromosomes.
     * @throws MathIllegalArgumentException if the population is not compatible with this {@link SelectionPolicy}
     */
    ChromosomePair select(Population population) throws MathIllegalArgumentException;
}
