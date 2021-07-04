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
package org.apache.commons.collections4.sequence;

import java.util.List;

/**
 * This interface is devoted to handle synchronized replacement sequences.
 *
 * @see ReplacementsFinder
 * @since 4.0
 */
public interface ReplacementsHandler<T> {

    /**
     * Handle two synchronized sequences.
     * <p>
     * This method is called by a {@link ReplacementsFinder ReplacementsFinder}
     * instance when it has synchronized two sub-sequences of object arrays
     * being compared, and at least one of the sequences is non-empty. Since the
     * sequences are synchronized, the objects before the two sub-sequences are
     * equals (if they exist). This property also holds for the objects after
     * the two sub-sequences.
     * <p>
     * The replacement is defined as replacing the <code>from</code>
     * sub-sequence into the <code>to</code> sub-sequence.
     *
     * @param skipped  number of tokens skipped since the last call (i.e. number of
     *   tokens that were in both sequences), this number should be strictly positive
     *   except on the very first call where it can be zero (if the first object of
     *   the two sequences are different)
     * @param from  sub-sequence of objects coming from the first sequence
     * @param to  sub-sequence of objects coming from the second sequence
     */
    void handleReplacement(int skipped, List<T> from, List<T> to);

}
