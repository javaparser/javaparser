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
/**
 * This package provides classes to compare two sequences of objects.
 * <p>
 * The two sequences can hold any object type, as only the
 * <code>equals</code> method is used to compare the elements of the
 * sequences. It is guaranteed that the comparisons will always be done
 * as <code>o1.equals(o2)</code> where <code>o1</code> belongs to the
 * first sequence and <code>o2</code> belongs to the second
 * sequence. This can be important if subclassing is used for some
 * elements in the first sequence and the <code>equals</code> method is
 * specialized.
 * <p>
 * Comparison can be seen from two points of view: either as giving the
 * smallest modification allowing to transform the first sequence into
 * the second one, or as giving the longest sequence which is a
 * subsequence of both initial sequences. The <code>equals</code> method
 * is used to compare objects, so any object can be put into
 * sequences. Modifications include deleting, inserting or keeping one
 * object, starting from the beginning of the first sequence. Like most
 * algorithms of the same type, objects transpositions are not
 * supported. This means that if a sequence <code>(A, B)</code> is
 * compared to <code>(B, A)</code>, the result will be either the
 * sequence of three commands <code>delete A</code>, <code>keep B</code>,
 * <code>insert A</code> or the sequence  <code>insert B</code>,
 * <code>keep A</code>, <code>delete B</code>.
 * <p>
 * The package uses a very efficient comparison algorithm designed by
 * Eugene W. Myers and described in his paper: <a
 * href="http://www.cis.upenn.edu/~bcpierce/courses/dd/papers/diff.ps">An O(ND)
 * Difference Algorithm and Its Variations</a>. This algorithm produces
 * the shortest possible
 * {@link org.apache.commons.collections4.sequence.EditScript edit script} containing
 * all the {@link org.apache.commons.collections4.sequence.EditCommand commands}
 * needed to transform the first sequence into the second one.
 * The entry point for the user to this algorithm is the
 * {@link org.apache.commons.collections4.sequence.SequencesComparator} class.
 * <p>
 * As explained in Gene Myers paper, the edit script is equivalent to all
 * other representations and contains all the needed information either
 * to perform the transformation, of course, or to retrieve the longest
 * common subsequence for example.
 * <p>
 * If the user needs a very fine grained access to the comparison result,
 * he needs to go through this script by providing a visitor implementing
 * the {@link org.apache.commons.collections4.sequence.CommandVisitor} interface.
 * <p>
 * Sometimes however, a more synthetic approach is needed. If the user
 * prefers to see the differences between the two sequences as global
 * <code>replacement</code> operations acting on complete subsequences of
 * the original sequences, he will provide an object implementing the
 * simple {@link org.apache.commons.collections4.sequence.ReplacementsHandler} interface,
 * using an instance of the {@link org.apache.commons.collections4.sequence.ReplacementsFinder}
 * class as a command converting layer between his object and the edit script. The number of
 * objects which are common to both initial arrays and hence are skipped between each call to the user
 * {@link org.apache.commons.collections4.sequence.ReplacementsHandler#handleReplacement handleReplacement}
 * method is also provided. This allows the user to keep track of the current index in
 * both arrays if he needs so.
 *
 */
package org.apache.commons.collections4.sequence;
