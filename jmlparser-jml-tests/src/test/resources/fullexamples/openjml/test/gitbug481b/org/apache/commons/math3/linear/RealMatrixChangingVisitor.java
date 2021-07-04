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

package org.apache.commons.math3.linear;

/**
 * Interface defining a visitor for matrix entries.
 *
 * @see DefaultRealMatrixChangingVisitor
 * @since 2.0
 */
public interface RealMatrixChangingVisitor {
    /**
     * Start visiting a matrix.
     * <p>This method is called once before any entry of the matrix is visited.</p>
     * @param rows number of rows of the matrix
     * @param columns number of columns of the matrix
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     */
    void start(int rows, int columns,
               int startRow, int endRow, int startColumn, int endColumn);

    /**
     * Visit one matrix entry.
     * @param row row index of the entry
     * @param column column index of the entry
     * @param value current value of the entry
     * @return the new value to be set for the entry
     */
    double visit(int row, int column, double value);

    /**
     * End visiting a matrix.
     * <p>This method is called once after all entries of the matrix have been visited.</p>
     * @return the value that the <code>walkInXxxOrder</code> must return
     */
    double end();
}
