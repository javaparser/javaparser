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

package org.apache.commons.math3.ode.nonstiff;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.linear.Array2DRowFieldMatrix;
import org.apache.commons.math3.linear.ArrayFieldVector;
import org.apache.commons.math3.linear.FieldDecompositionSolver;
import org.apache.commons.math3.linear.FieldLUDecomposition;
import org.apache.commons.math3.linear.FieldMatrix;
import org.apache.commons.math3.util.MathArrays;

/** Transformer to Nordsieck vectors for Adams integrators.
 * <p>This class is used by {@link AdamsBashforthIntegrator Adams-Bashforth} and
 * {@link AdamsMoultonIntegrator Adams-Moulton} integrators to convert between
 * classical representation with several previous first derivatives and Nordsieck
 * representation with higher order scaled derivatives.</p>
 *
 * <p>We define scaled derivatives s<sub>i</sub>(n) at step n as:
 * <pre>
 * s<sub>1</sub>(n) = h y'<sub>n</sub> for first derivative
 * s<sub>2</sub>(n) = h<sup>2</sup>/2 y''<sub>n</sub> for second derivative
 * s<sub>3</sub>(n) = h<sup>3</sup>/6 y'''<sub>n</sub> for third derivative
 * ...
 * s<sub>k</sub>(n) = h<sup>k</sup>/k! y<sup>(k)</sup><sub>n</sub> for k<sup>th</sup> derivative
 * </pre></p>
 *
 * <p>With the previous definition, the classical representation of multistep methods
 * uses first derivatives only, i.e. it handles y<sub>n</sub>, s<sub>1</sub>(n) and
 * q<sub>n</sub> where q<sub>n</sub> is defined as:
 * <pre>
 *   q<sub>n</sub> = [ s<sub>1</sub>(n-1) s<sub>1</sub>(n-2) ... s<sub>1</sub>(n-(k-1)) ]<sup>T</sup>
 * </pre>
 * (we omit the k index in the notation for clarity).</p>
 *
 * <p>Another possible representation uses the Nordsieck vector with
 * higher degrees scaled derivatives all taken at the same step, i.e it handles y<sub>n</sub>,
 * s<sub>1</sub>(n) and r<sub>n</sub>) where r<sub>n</sub> is defined as:
 * <pre>
 * r<sub>n</sub> = [ s<sub>2</sub>(n), s<sub>3</sub>(n) ... s<sub>k</sub>(n) ]<sup>T</sup>
 * </pre>
 * (here again we omit the k index in the notation for clarity)
 * </p>
 *
 * <p>Taylor series formulas show that for any index offset i, s<sub>1</sub>(n-i) can be
 * computed from s<sub>1</sub>(n), s<sub>2</sub>(n) ... s<sub>k</sub>(n), the formula being exact
 * for degree k polynomials.
 * <pre>
 * s<sub>1</sub>(n-i) = s<sub>1</sub>(n) + &sum;<sub>j&gt;0</sub> (j+1) (-i)<sup>j</sup> s<sub>j+1</sub>(n)
 * </pre>
 * The previous formula can be used with several values for i to compute the transform between
 * classical representation and Nordsieck vector at step end. The transform between r<sub>n</sub>
 * and q<sub>n</sub> resulting from the Taylor series formulas above is:
 * <pre>
 * q<sub>n</sub> = s<sub>1</sub>(n) u + P r<sub>n</sub>
 * </pre>
 * where u is the [ 1 1 ... 1 ]<sup>T</sup> vector and P is the (k-1)&times;(k-1) matrix built
 * with the (j+1) (-i)<sup>j</sup> terms with i being the row number starting from 1 and j being
 * the column number starting from 1:
 * <pre>
 *        [  -2   3   -4    5  ... ]
 *        [  -4  12  -32   80  ... ]
 *   P =  [  -6  27 -108  405  ... ]
 *        [  -8  48 -256 1280  ... ]
 *        [          ...           ]
 * </pre></p>
 *
 * <p>Changing -i into +i in the formula above can be used to compute a similar transform between
 * classical representation and Nordsieck vector at step start. The resulting matrix is simply
 * the absolute value of matrix P.</p>
 *
 * <p>For {@link AdamsBashforthIntegrator Adams-Bashforth} method, the Nordsieck vector
 * at step n+1 is computed from the Nordsieck vector at step n as follows:
 * <ul>
 *   <li>y<sub>n+1</sub> = y<sub>n</sub> + s<sub>1</sub>(n) + u<sup>T</sup> r<sub>n</sub></li>
 *   <li>s<sub>1</sub>(n+1) = h f(t<sub>n+1</sub>, y<sub>n+1</sub>)</li>
 *   <li>r<sub>n+1</sub> = (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u + P<sup>-1</sup> A P r<sub>n</sub></li>
 * </ul>
 * where A is a rows shifting matrix (the lower left part is an identity matrix):
 * <pre>
 *        [ 0 0   ...  0 0 | 0 ]
 *        [ ---------------+---]
 *        [ 1 0   ...  0 0 | 0 ]
 *    A = [ 0 1   ...  0 0 | 0 ]
 *        [       ...      | 0 ]
 *        [ 0 0   ...  1 0 | 0 ]
 *        [ 0 0   ...  0 1 | 0 ]
 * </pre></p>
 *
 * <p>For {@link AdamsMoultonIntegrator Adams-Moulton} method, the predicted Nordsieck vector
 * at step n+1 is computed from the Nordsieck vector at step n as follows:
 * <ul>
 *   <li>Y<sub>n+1</sub> = y<sub>n</sub> + s<sub>1</sub>(n) + u<sup>T</sup> r<sub>n</sub></li>
 *   <li>S<sub>1</sub>(n+1) = h f(t<sub>n+1</sub>, Y<sub>n+1</sub>)</li>
 *   <li>R<sub>n+1</sub> = (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u + P<sup>-1</sup> A P r<sub>n</sub></li>
 * </ul>
 * From this predicted vector, the corrected vector is computed as follows:
 * <ul>
 *   <li>y<sub>n+1</sub> = y<sub>n</sub> + S<sub>1</sub>(n+1) + [ -1 +1 -1 +1 ... &plusmn;1 ] r<sub>n+1</sub></li>
 *   <li>s<sub>1</sub>(n+1) = h f(t<sub>n+1</sub>, y<sub>n+1</sub>)</li>
 *   <li>r<sub>n+1</sub> = R<sub>n+1</sub> + (s<sub>1</sub>(n+1) - S<sub>1</sub>(n+1)) P<sup>-1</sup> u</li>
 * </ul>
 * where the upper case Y<sub>n+1</sub>, S<sub>1</sub>(n+1) and R<sub>n+1</sub> represent the
 * predicted states whereas the lower case y<sub>n+1</sub>, s<sub>n+1</sub> and r<sub>n+1</sub>
 * represent the corrected states.</p>
 *
 * <p>We observe that both methods use similar update formulas. In both cases a P<sup>-1</sup>u
 * vector and a P<sup>-1</sup> A P matrix are used that do not depend on the state,
 * they only depend on k. This class handles these transformations.</p>
 *
 * @param <T> the type of the field elements
 * @since 3.6
 */
public class AdamsNordsieckFieldTransformer<T extends RealFieldElement<T>> {

    /** Cache for already computed coefficients. */
    private static final Map<Integer,
                         Map<Field<? extends RealFieldElement<?>>,
                                   AdamsNordsieckFieldTransformer<? extends RealFieldElement<?>>>> CACHE =
        new HashMap<Integer, Map<Field<? extends RealFieldElement<?>>,
                                 AdamsNordsieckFieldTransformer<? extends RealFieldElement<?>>>>();

    /** Field to which the time and state vector elements belong. */
    private final Field<T> field;

    /** Update matrix for the higher order derivatives h<sup>2</sup>/2 y'', h<sup>3</sup>/6 y''' ... */
    private final Array2DRowFieldMatrix<T> update;

    /** Update coefficients of the higher order derivatives wrt y'. */
    private final T[] c1;

    /** Simple constructor.
     * @param field field to which the time and state vector elements belong
     * @param n number of steps of the multistep method
     * (excluding the one being computed)
     */
    private AdamsNordsieckFieldTransformer(final Field<T> field, final int n) {

        this.field = field;
        final int rows = n - 1;

        // compute coefficients
        FieldMatrix<T> bigP = buildP(rows);
        FieldDecompositionSolver<T> pSolver =
            new FieldLUDecomposition<T>(bigP).getSolver();

        T[] u = MathArrays.buildArray(field, rows);
        Arrays.fill(u, field.getOne());
        c1 = pSolver.solve(new ArrayFieldVector<T>(u, false)).toArray();

        // update coefficients are computed by combining transform from
        // Nordsieck to multistep, then shifting rows to represent step advance
        // then applying inverse transform
        T[][] shiftedP = bigP.getData();
        for (int i = shiftedP.length - 1; i > 0; --i) {
            // shift rows
            shiftedP[i] = shiftedP[i - 1];
        }
        shiftedP[0] = MathArrays.buildArray(field, rows);
        Arrays.fill(shiftedP[0], field.getZero());
        update = new Array2DRowFieldMatrix<T>(pSolver.solve(new Array2DRowFieldMatrix<T>(shiftedP, false)).getData());

    }

    /** Get the Nordsieck transformer for a given field and number of steps.
     * @param field field to which the time and state vector elements belong
     * @param nSteps number of steps of the multistep method
     * (excluding the one being computed)
     * @return Nordsieck transformer for the specified field and number of steps
     * @param <T> the type of the field elements
     */
    @SuppressWarnings("unchecked")
    public static <T extends RealFieldElement<T>> AdamsNordsieckFieldTransformer<T>
    getInstance(final Field<T> field, final int nSteps) {
        synchronized(CACHE) {
            Map<Field<? extends RealFieldElement<?>>,
                      AdamsNordsieckFieldTransformer<? extends RealFieldElement<?>>> map = CACHE.get(nSteps);
            if (map == null) {
                map = new HashMap<Field<? extends RealFieldElement<?>>,
                                        AdamsNordsieckFieldTransformer<? extends RealFieldElement<?>>>();
                CACHE.put(nSteps, map);
            }
            @SuppressWarnings("rawtypes") // use rawtype to avoid compilation problems with java 1.5
            AdamsNordsieckFieldTransformer t = map.get(field);
            if (t == null) {
                t = new AdamsNordsieckFieldTransformer<T>(field, nSteps);
                map.put(field, (AdamsNordsieckFieldTransformer<T>) t);
            }
            return (AdamsNordsieckFieldTransformer<T>) t;

        }
    }

    /** Build the P matrix.
     * <p>The P matrix general terms are shifted (j+1) (-i)<sup>j</sup> terms
     * with i being the row number starting from 1 and j being the column
     * number starting from 1:
     * <pre>
     *        [  -2   3   -4    5  ... ]
     *        [  -4  12  -32   80  ... ]
     *   P =  [  -6  27 -108  405  ... ]
     *        [  -8  48 -256 1280  ... ]
     *        [          ...           ]
     * </pre></p>
     * @param rows number of rows of the matrix
     * @return P matrix
     */
    private FieldMatrix<T> buildP(final int rows) {

        final T[][] pData = MathArrays.buildArray(field, rows, rows);

        for (int i = 1; i <= pData.length; ++i) {
            // build the P matrix elements from Taylor series formulas
            final T[] pI = pData[i - 1];
            final int factor = -i;
            T aj = field.getZero().add(factor);
            for (int j = 1; j <= pI.length; ++j) {
                pI[j - 1] = aj.multiply(j + 1);
                aj = aj.multiply(factor);
            }
        }

        return new Array2DRowFieldMatrix<T>(pData, false);

    }

    /** Initialize the high order scaled derivatives at step start.
     * @param h step size to use for scaling
     * @param t first steps times
     * @param y first steps states
     * @param yDot first steps derivatives
     * @return Nordieck vector at start of first step (h<sup>2</sup>/2 y''<sub>n</sub>,
     * h<sup>3</sup>/6 y'''<sub>n</sub> ... h<sup>k</sup>/k! y<sup>(k)</sup><sub>n</sub>)
     */

    public Array2DRowFieldMatrix<T> initializeHighOrderDerivatives(final T h, final T[] t,
                                                                   final T[][] y,
                                                                   final T[][] yDot) {

        // using Taylor series with di = ti - t0, we get:
        //  y(ti)  - y(t0)  - di y'(t0) =   di^2 / h^2 s2 + ... +   di^k     / h^k sk + O(h^k)
        //  y'(ti) - y'(t0)             = 2 di   / h^2 s2 + ... + k di^(k-1) / h^k sk + O(h^(k-1))
        // we write these relations for i = 1 to i= 1+n/2 as a set of n + 2 linear
        // equations depending on the Nordsieck vector [s2 ... sk rk], so s2 to sk correspond
        // to the appropriately truncated Taylor expansion, and rk is the Taylor remainder.
        // The goal is to have s2 to sk as accurate as possible considering the fact the sum is
        // truncated and we don't want the error terms to be included in s2 ... sk, so we need
        // to solve also for the remainder
        final T[][] a     = MathArrays.buildArray(field, c1.length + 1, c1.length + 1);
        final T[][] b     = MathArrays.buildArray(field, c1.length + 1, y[0].length);
        final T[]   y0    = y[0];
        final T[]   yDot0 = yDot[0];
        for (int i = 1; i < y.length; ++i) {

            final T di    = t[i].subtract(t[0]);
            final T ratio = di.divide(h);
            T dikM1Ohk    = h.reciprocal();

            // linear coefficients of equations
            // y(ti) - y(t0) - di y'(t0) and y'(ti) - y'(t0)
            final T[] aI    = a[2 * i - 2];
            final T[] aDotI = (2 * i - 1) < a.length ? a[2 * i - 1] : null;
            for (int j = 0; j < aI.length; ++j) {
                dikM1Ohk = dikM1Ohk.multiply(ratio);
                aI[j]    = di.multiply(dikM1Ohk);
                if (aDotI != null) {
                    aDotI[j]  = dikM1Ohk.multiply(j + 2);
                }
            }

            // expected value of the previous equations
            final T[] yI    = y[i];
            final T[] yDotI = yDot[i];
            final T[] bI    = b[2 * i - 2];
            final T[] bDotI = (2 * i - 1) < b.length ? b[2 * i - 1] : null;
            for (int j = 0; j < yI.length; ++j) {
                bI[j]    = yI[j].subtract(y0[j]).subtract(di.multiply(yDot0[j]));
                if (bDotI != null) {
                    bDotI[j] = yDotI[j].subtract(yDot0[j]);
                }
            }

        }

        // solve the linear system to get the best estimate of the Nordsieck vector [s2 ... sk],
        // with the additional terms s(k+1) and c grabbing the parts after the truncated Taylor expansion
        final FieldLUDecomposition<T> decomposition = new FieldLUDecomposition<T>(new Array2DRowFieldMatrix<T>(a, false));
        final FieldMatrix<T> x = decomposition.getSolver().solve(new Array2DRowFieldMatrix<T>(b, false));

        // extract just the Nordsieck vector [s2 ... sk]
        final Array2DRowFieldMatrix<T> truncatedX =
                        new Array2DRowFieldMatrix<T>(field, x.getRowDimension() - 1, x.getColumnDimension());
        for (int i = 0; i < truncatedX.getRowDimension(); ++i) {
            for (int j = 0; j < truncatedX.getColumnDimension(); ++j) {
                truncatedX.setEntry(i, j, x.getEntry(i, j));
            }
        }
        return truncatedX;

    }

    /** Update the high order scaled derivatives for Adams integrators (phase 1).
     * <p>The complete update of high order derivatives has a form similar to:
     * <pre>
     * r<sub>n+1</sub> = (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u + P<sup>-1</sup> A P r<sub>n</sub>
     * </pre>
     * this method computes the P<sup>-1</sup> A P r<sub>n</sub> part.</p>
     * @param highOrder high order scaled derivatives
     * (h<sup>2</sup>/2 y'', ... h<sup>k</sup>/k! y(k))
     * @return updated high order derivatives
     * @see #updateHighOrderDerivativesPhase2(RealFieldElement[], RealFieldElement[], Array2DRowFieldMatrix)
     */
    public Array2DRowFieldMatrix<T> updateHighOrderDerivativesPhase1(final Array2DRowFieldMatrix<T> highOrder) {
        return update.multiply(highOrder);
    }

    /** Update the high order scaled derivatives Adams integrators (phase 2).
     * <p>The complete update of high order derivatives has a form similar to:
     * <pre>
     * r<sub>n+1</sub> = (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u + P<sup>-1</sup> A P r<sub>n</sub>
     * </pre>
     * this method computes the (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u part.</p>
     * <p>Phase 1 of the update must already have been performed.</p>
     * @param start first order scaled derivatives at step start
     * @param end first order scaled derivatives at step end
     * @param highOrder high order scaled derivatives, will be modified
     * (h<sup>2</sup>/2 y'', ... h<sup>k</sup>/k! y(k))
     * @see #updateHighOrderDerivativesPhase1(Array2DRowFieldMatrix)
     */
    public void updateHighOrderDerivativesPhase2(final T[] start,
                                                 final T[] end,
                                                 final Array2DRowFieldMatrix<T> highOrder) {
        final T[][] data = highOrder.getDataRef();
        for (int i = 0; i < data.length; ++i) {
            final T[] dataI = data[i];
            final T c1I = c1[i];
            for (int j = 0; j < dataI.length; ++j) {
                dataI[j] = dataI[j].add(c1I.multiply(start[j].subtract(end[j])));
            }
        }
    }

}
