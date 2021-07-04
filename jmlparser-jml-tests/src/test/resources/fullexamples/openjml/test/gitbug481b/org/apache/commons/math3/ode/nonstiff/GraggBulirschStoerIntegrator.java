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

import org.apache.commons.math3.analysis.solvers.UnivariateSolver;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.ode.ExpandableStatefulODE;
import org.apache.commons.math3.ode.events.EventHandler;
import org.apache.commons.math3.ode.sampling.AbstractStepInterpolator;
import org.apache.commons.math3.ode.sampling.StepHandler;
import org.apache.commons.math3.util.FastMath;

/**
 * This class implements a Gragg-Bulirsch-Stoer integrator for
 * Ordinary Differential Equations.
 *
 * <p>The Gragg-Bulirsch-Stoer algorithm is one of the most efficient
 * ones currently available for smooth problems. It uses Richardson
 * extrapolation to estimate what would be the solution if the step
 * size could be decreased down to zero.</p>
 *
 * <p>
 * This method changes both the step size and the order during
 * integration, in order to minimize computation cost. It is
 * particularly well suited when a very high precision is needed. The
 * limit where this method becomes more efficient than high-order
 * embedded Runge-Kutta methods like {@link DormandPrince853Integrator
 * Dormand-Prince 8(5,3)} depends on the problem. Results given in the
 * Hairer, Norsett and Wanner book show for example that this limit
 * occurs for accuracy around 1e-6 when integrating Saltzam-Lorenz
 * equations (the authors note this problem is <i>extremely sensitive
 * to the errors in the first integration steps</i>), and around 1e-11
 * for a two dimensional celestial mechanics problems with seven
 * bodies (pleiades problem, involving quasi-collisions for which
 * <i>automatic step size control is essential</i>).
 * </p>
 *
 * <p>
 * This implementation is basically a reimplementation in Java of the
 * <a
 * href="http://www.unige.ch/math/folks/hairer/prog/nonstiff/odex.f">odex</a>
 * fortran code by E. Hairer and G. Wanner. The redistribution policy
 * for this code is available <a
 * href="http://www.unige.ch/~hairer/prog/licence.txt">here</a>, for
 * convenience, it is reproduced below.</p>
 * </p>
 *
 * <table border="0" width="80%" cellpadding="10" align="center" bgcolor="#E0E0E0">
 * <tr><td>Copyright (c) 2004, Ernst Hairer</td></tr>
 *
 * <tr><td>Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 * <ul>
 *  <li>Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.</li>
 *  <li>Redistributions in binary form must reproduce the above copyright
 *      notice, this list of conditions and the following disclaimer in the
 *      documentation and/or other materials provided with the distribution.</li>
 * </ul></td></tr>
 *
 * <tr><td><strong>THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,
 * BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.</strong></td></tr>
 * </table>
 *
 * @since 1.2
 */

public class GraggBulirschStoerIntegrator extends AdaptiveStepsizeIntegrator {

    /** Integrator method name. */
    private static final String METHOD_NAME = "Gragg-Bulirsch-Stoer";

    /** maximal order. */
    private int maxOrder;

    /** step size sequence. */
    private int[] sequence;

    /** overall cost of applying step reduction up to iteration k+1, in number of calls. */
    private int[] costPerStep;

    /** cost per unit step. */
    private double[] costPerTimeUnit;

    /** optimal steps for each order. */
    private double[] optimalStep;

    /** extrapolation coefficients. */
    private double[][] coeff;

    /** stability check enabling parameter. */
    private boolean performTest;

    /** maximal number of checks for each iteration. */
    private int maxChecks;

    /** maximal number of iterations for which checks are performed. */
    private int maxIter;

    /** stepsize reduction factor in case of stability check failure. */
    private double stabilityReduction;

    /** first stepsize control factor. */
    private double stepControl1;

    /** second stepsize control factor. */
    private double stepControl2;

    /** third stepsize control factor. */
    private double stepControl3;

    /** fourth stepsize control factor. */
    private double stepControl4;

    /** first order control factor. */
    private double orderControl1;

    /** second order control factor. */
    private double orderControl2;

    /** use interpolation error in stepsize control. */
    private boolean useInterpolationError;

    /** interpolation order control parameter. */
    private int mudif;

  /** Simple constructor.
   * Build a Gragg-Bulirsch-Stoer integrator with the given step
   * bounds. All tuning parameters are set to their default
   * values. The default step handler does nothing.
   * @param minStep minimal step (sign is irrelevant, regardless of
   * integration direction, forward or backward), the last step can
   * be smaller than this
   * @param maxStep maximal step (sign is irrelevant, regardless of
   * integration direction, forward or backward), the last step can
   * be smaller than this
   * @param scalAbsoluteTolerance allowed absolute error
   * @param scalRelativeTolerance allowed relative error
   */
  public GraggBulirschStoerIntegrator(final double minStep, final double maxStep,
                                      final double scalAbsoluteTolerance,
                                      final double scalRelativeTolerance) {
    super(METHOD_NAME, minStep, maxStep,
          scalAbsoluteTolerance, scalRelativeTolerance);
    setStabilityCheck(true, -1, -1, -1);
    setControlFactors(-1, -1, -1, -1);
    setOrderControl(-1, -1, -1);
    setInterpolationControl(true, -1);
  }

  /** Simple constructor.
   * Build a Gragg-Bulirsch-Stoer integrator with the given step
   * bounds. All tuning parameters are set to their default
   * values. The default step handler does nothing.
   * @param minStep minimal step (must be positive even for backward
   * integration), the last step can be smaller than this
   * @param maxStep maximal step (must be positive even for backward
   * integration)
   * @param vecAbsoluteTolerance allowed absolute error
   * @param vecRelativeTolerance allowed relative error
   */
  public GraggBulirschStoerIntegrator(final double minStep, final double maxStep,
                                      final double[] vecAbsoluteTolerance,
                                      final double[] vecRelativeTolerance) {
    super(METHOD_NAME, minStep, maxStep,
          vecAbsoluteTolerance, vecRelativeTolerance);
    setStabilityCheck(true, -1, -1, -1);
    setControlFactors(-1, -1, -1, -1);
    setOrderControl(-1, -1, -1);
    setInterpolationControl(true, -1);
  }

  /** Set the stability check controls.
   * <p>The stability check is performed on the first few iterations of
   * the extrapolation scheme. If this test fails, the step is rejected
   * and the stepsize is reduced.</p>
   * <p>By default, the test is performed, at most during two
   * iterations at each step, and at most once for each of these
   * iterations. The default stepsize reduction factor is 0.5.</p>
   * @param performStabilityCheck if true, stability check will be performed,
     if false, the check will be skipped
   * @param maxNumIter maximal number of iterations for which checks are
   * performed (the number of iterations is reset to default if negative
   * or null)
   * @param maxNumChecks maximal number of checks for each iteration
   * (the number of checks is reset to default if negative or null)
   * @param stepsizeReductionFactor stepsize reduction factor in case of
   * failure (the factor is reset to default if lower than 0.0001 or
   * greater than 0.9999)
   */
  public void setStabilityCheck(final boolean performStabilityCheck,
                                final int maxNumIter, final int maxNumChecks,
                                final double stepsizeReductionFactor) {

    this.performTest = performStabilityCheck;
    this.maxIter     = (maxNumIter   <= 0) ? 2 : maxNumIter;
    this.maxChecks   = (maxNumChecks <= 0) ? 1 : maxNumChecks;

    if ((stepsizeReductionFactor < 0.0001) || (stepsizeReductionFactor > 0.9999)) {
      this.stabilityReduction = 0.5;
    } else {
      this.stabilityReduction = stepsizeReductionFactor;
    }

  }

  /** Set the step size control factors.

   * <p>The new step size hNew is computed from the old one h by:
   * <pre>
   * hNew = h * stepControl2 / (err/stepControl1)^(1/(2k+1))
   * </pre>
   * where err is the scaled error and k the iteration number of the
   * extrapolation scheme (counting from 0). The default values are
   * 0.65 for stepControl1 and 0.94 for stepControl2.</p>
   * <p>The step size is subject to the restriction:
   * <pre>
   * stepControl3^(1/(2k+1))/stepControl4 <= hNew/h <= 1/stepControl3^(1/(2k+1))
   * </pre>
   * The default values are 0.02 for stepControl3 and 4.0 for
   * stepControl4.</p>
   * @param control1 first stepsize control factor (the factor is
   * reset to default if lower than 0.0001 or greater than 0.9999)
   * @param control2 second stepsize control factor (the factor
   * is reset to default if lower than 0.0001 or greater than 0.9999)
   * @param control3 third stepsize control factor (the factor is
   * reset to default if lower than 0.0001 or greater than 0.9999)
   * @param control4 fourth stepsize control factor (the factor
   * is reset to default if lower than 1.0001 or greater than 999.9)
   */
  public void setControlFactors(final double control1, final double control2,
                                final double control3, final double control4) {

    if ((control1 < 0.0001) || (control1 > 0.9999)) {
      this.stepControl1 = 0.65;
    } else {
      this.stepControl1 = control1;
    }

    if ((control2 < 0.0001) || (control2 > 0.9999)) {
      this.stepControl2 = 0.94;
    } else {
      this.stepControl2 = control2;
    }

    if ((control3 < 0.0001) || (control3 > 0.9999)) {
      this.stepControl3 = 0.02;
    } else {
      this.stepControl3 = control3;
    }

    if ((control4 < 1.0001) || (control4 > 999.9)) {
      this.stepControl4 = 4.0;
    } else {
      this.stepControl4 = control4;
    }

  }

  /** Set the order control parameters.
   * <p>The Gragg-Bulirsch-Stoer method changes both the step size and
   * the order during integration, in order to minimize computation
   * cost. Each extrapolation step increases the order by 2, so the
   * maximal order that will be used is always even, it is twice the
   * maximal number of columns in the extrapolation table.</p>
   * <pre>
   * order is decreased if w(k-1) <= w(k)   * orderControl1
   * order is increased if w(k)   <= w(k-1) * orderControl2
   * </pre>
   * <p>where w is the table of work per unit step for each order
   * (number of function calls divided by the step length), and k is
   * the current order.</p>
   * <p>The default maximal order after construction is 18 (i.e. the
   * maximal number of columns is 9). The default values are 0.8 for
   * orderControl1 and 0.9 for orderControl2.</p>
   * @param maximalOrder maximal order in the extrapolation table (the
   * maximal order is reset to default if order <= 6 or odd)
   * @param control1 first order control factor (the factor is
   * reset to default if lower than 0.0001 or greater than 0.9999)
   * @param control2 second order control factor (the factor
   * is reset to default if lower than 0.0001 or greater than 0.9999)
   */
  public void setOrderControl(final int maximalOrder,
                              final double control1, final double control2) {

    if ((maximalOrder <= 6) || (maximalOrder % 2 != 0)) {
      this.maxOrder = 18;
    }

    if ((control1 < 0.0001) || (control1 > 0.9999)) {
      this.orderControl1 = 0.8;
    } else {
      this.orderControl1 = control1;
    }

    if ((control2 < 0.0001) || (control2 > 0.9999)) {
      this.orderControl2 = 0.9;
    } else {
      this.orderControl2 = control2;
    }

    // reinitialize the arrays
    initializeArrays();

  }

  /** {@inheritDoc} */
  @Override
  public void addStepHandler (final StepHandler handler) {

    super.addStepHandler(handler);

    // reinitialize the arrays
    initializeArrays();

  }

  /** {@inheritDoc} */
  @Override
  public void addEventHandler(final EventHandler function,
                              final double maxCheckInterval,
                              final double convergence,
                              final int maxIterationCount,
                              final UnivariateSolver solver) {
    super.addEventHandler(function, maxCheckInterval, convergence,
                          maxIterationCount, solver);

    // reinitialize the arrays
    initializeArrays();

  }

  /** Initialize the integrator internal arrays. */
  private void initializeArrays() {

    final int size = maxOrder / 2;

    if ((sequence == null) || (sequence.length != size)) {
      // all arrays should be reallocated with the right size
      sequence        = new int[size];
      costPerStep     = new int[size];
      coeff           = new double[size][];
      costPerTimeUnit = new double[size];
      optimalStep     = new double[size];
    }

    // step size sequence: 2, 6, 10, 14, ...
    for (int k = 0; k < size; ++k) {
        sequence[k] = 4 * k + 2;
    }

    // initialize the order selection cost array
    // (number of function calls for each column of the extrapolation table)
    costPerStep[0] = sequence[0] + 1;
    for (int k = 1; k < size; ++k) {
      costPerStep[k] = costPerStep[k-1] + sequence[k];
    }

    // initialize the extrapolation tables
    for (int k = 0; k < size; ++k) {
      coeff[k] = (k > 0) ? new double[k] : null;
      for (int l = 0; l < k; ++l) {
        final double ratio = ((double) sequence[k]) / sequence[k-l-1];
        coeff[k][l] = 1.0 / (ratio * ratio - 1.0);
      }
    }

  }

  /** Set the interpolation order control parameter.
   * The interpolation order for dense output is 2k - mudif + 1. The
   * default value for mudif is 4 and the interpolation error is used
   * in stepsize control by default.

   * @param useInterpolationErrorForControl if true, interpolation error is used
   * for stepsize control
   * @param mudifControlParameter interpolation order control parameter (the parameter
   * is reset to default if <= 0 or >= 7)
   */
  public void setInterpolationControl(final boolean useInterpolationErrorForControl,
                                      final int mudifControlParameter) {

    this.useInterpolationError = useInterpolationErrorForControl;

    if ((mudifControlParameter <= 0) || (mudifControlParameter >= 7)) {
      this.mudif = 4;
    } else {
      this.mudif = mudifControlParameter;
    }

  }

  /** Update scaling array.
   * @param y1 first state vector to use for scaling
   * @param y2 second state vector to use for scaling
   * @param scale scaling array to update (can be shorter than state)
   */
  private void rescale(final double[] y1, final double[] y2, final double[] scale) {
    if (vecAbsoluteTolerance == null) {
      for (int i = 0; i < scale.length; ++i) {
        final double yi = FastMath.max(FastMath.abs(y1[i]), FastMath.abs(y2[i]));
        scale[i] = scalAbsoluteTolerance + scalRelativeTolerance * yi;
      }
    } else {
      for (int i = 0; i < scale.length; ++i) {
        final double yi = FastMath.max(FastMath.abs(y1[i]), FastMath.abs(y2[i]));
        scale[i] = vecAbsoluteTolerance[i] + vecRelativeTolerance[i] * yi;
      }
    }
  }

  /** Perform integration over one step using substeps of a modified
   * midpoint method.
   * @param t0 initial time
   * @param y0 initial value of the state vector at t0
   * @param step global step
   * @param k iteration number (from 0 to sequence.length - 1)
   * @param scale scaling array (can be shorter than state)
   * @param f placeholder where to put the state vector derivatives at each substep
   *          (element 0 already contains initial derivative)
   * @param yMiddle placeholder where to put the state vector at the middle of the step
   * @param yEnd placeholder where to put the state vector at the end
   * @param yTmp placeholder for one state vector
   * @return true if computation was done properly,
   *         false if stability check failed before end of computation
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   * @exception DimensionMismatchException if arrays dimensions do not match equations settings
   */
  private boolean tryStep(final double t0, final double[] y0, final double step, final int k,
                          final double[] scale, final double[][] f,
                          final double[] yMiddle, final double[] yEnd,
                          final double[] yTmp)
      throws MaxCountExceededException, DimensionMismatchException {

    final int    n        = sequence[k];
    final double subStep  = step / n;
    final double subStep2 = 2 * subStep;

    // first substep
    double t = t0 + subStep;
    for (int i = 0; i < y0.length; ++i) {
      yTmp[i] = y0[i];
      yEnd[i] = y0[i] + subStep * f[0][i];
    }
    computeDerivatives(t, yEnd, f[1]);

    // other substeps
    for (int j = 1; j < n; ++j) {

      if (2 * j == n) {
        // save the point at the middle of the step
        System.arraycopy(yEnd, 0, yMiddle, 0, y0.length);
      }

      t += subStep;
      for (int i = 0; i < y0.length; ++i) {
        final double middle = yEnd[i];
        yEnd[i]       = yTmp[i] + subStep2 * f[j][i];
        yTmp[i]       = middle;
      }

      computeDerivatives(t, yEnd, f[j+1]);

      // stability check
      if (performTest && (j <= maxChecks) && (k < maxIter)) {
        double initialNorm = 0.0;
        for (int l = 0; l < scale.length; ++l) {
          final double ratio = f[0][l] / scale[l];
          initialNorm += ratio * ratio;
        }
        double deltaNorm = 0.0;
        for (int l = 0; l < scale.length; ++l) {
          final double ratio = (f[j+1][l] - f[0][l]) / scale[l];
          deltaNorm += ratio * ratio;
        }
        if (deltaNorm > 4 * FastMath.max(1.0e-15, initialNorm)) {
          return false;
        }
      }

    }

    // correction of the last substep (at t0 + step)
    for (int i = 0; i < y0.length; ++i) {
      yEnd[i] = 0.5 * (yTmp[i] + yEnd[i] + subStep * f[n][i]);
    }

    return true;

  }

  /** Extrapolate a vector.
   * @param offset offset to use in the coefficients table
   * @param k index of the last updated point
   * @param diag working diagonal of the Aitken-Neville's
   * triangle, without the last element
   * @param last last element
   */
  private void extrapolate(final int offset, final int k,
                           final double[][] diag, final double[] last) {

    // update the diagonal
    for (int j = 1; j < k; ++j) {
      for (int i = 0; i < last.length; ++i) {
        // Aitken-Neville's recursive formula
        diag[k-j-1][i] = diag[k-j][i] +
                         coeff[k+offset][j-1] * (diag[k-j][i] - diag[k-j-1][i]);
      }
    }

    // update the last element
    for (int i = 0; i < last.length; ++i) {
      // Aitken-Neville's recursive formula
      last[i] = diag[0][i] + coeff[k+offset][k-1] * (diag[0][i] - last[i]);
    }
  }

  /** {@inheritDoc} */
  @Override
  public void integrate(final ExpandableStatefulODE equations, final double t)
      throws NumberIsTooSmallException, DimensionMismatchException,
             MaxCountExceededException, NoBracketingException {

    sanityChecks(equations, t);
    setEquations(equations);
    final boolean forward = t > equations.getTime();

    // create some internal working arrays
    final double[] y0      = equations.getCompleteState();
    final double[] y       = y0.clone();
    final double[] yDot0   = new double[y.length];
    final double[] y1      = new double[y.length];
    final double[] yTmp    = new double[y.length];
    final double[] yTmpDot = new double[y.length];

    final double[][] diagonal = new double[sequence.length-1][];
    final double[][] y1Diag = new double[sequence.length-1][];
    for (int k = 0; k < sequence.length-1; ++k) {
      diagonal[k] = new double[y.length];
      y1Diag[k] = new double[y.length];
    }

    final double[][][] fk  = new double[sequence.length][][];
    for (int k = 0; k < sequence.length; ++k) {

      fk[k]    = new double[sequence[k] + 1][];

      // all substeps start at the same point, so share the first array
      fk[k][0] = yDot0;

      for (int l = 0; l < sequence[k]; ++l) {
        fk[k][l+1] = new double[y0.length];
      }

    }

    if (y != y0) {
      System.arraycopy(y0, 0, y, 0, y0.length);
    }

    final double[] yDot1 = new double[y0.length];
    final double[][] yMidDots = new double[1 + 2 * sequence.length][y0.length];

    // initial scaling
    final double[] scale = new double[mainSetDimension];
    rescale(y, y, scale);

    // initial order selection
    final double tol =
        (vecRelativeTolerance == null) ? scalRelativeTolerance : vecRelativeTolerance[0];
    final double log10R = FastMath.log10(FastMath.max(1.0e-10, tol));
    int targetIter = FastMath.max(1,
                              FastMath.min(sequence.length - 2,
                                       (int) FastMath.floor(0.5 - 0.6 * log10R)));

    // set up an interpolator sharing the integrator arrays
    final AbstractStepInterpolator interpolator =
            new GraggBulirschStoerStepInterpolator(y, yDot0,
                                                   y1, yDot1,
                                                   yMidDots, forward,
                                                   equations.getPrimaryMapper(),
                                                   equations.getSecondaryMappers());
    interpolator.storeTime(equations.getTime());

    stepStart = equations.getTime();
    double  hNew             = 0;
    double  maxError         = Double.MAX_VALUE;
    boolean previousRejected = false;
    boolean firstTime        = true;
    boolean newStep          = true;
    boolean firstStepAlreadyComputed = false;
    initIntegration(equations.getTime(), y0, t);
    costPerTimeUnit[0] = 0;
    isLastStep = false;
    do {

      double error;
      boolean reject = false;

      if (newStep) {

        interpolator.shift();

        // first evaluation, at the beginning of the step
        if (! firstStepAlreadyComputed) {
          computeDerivatives(stepStart, y, yDot0);
        }

        if (firstTime) {
          hNew = initializeStep(forward, 2 * targetIter + 1, scale,
                                stepStart, y, yDot0, yTmp, yTmpDot);
        }

        newStep = false;

      }

      stepSize = hNew;

      // step adjustment near bounds
      if ((forward && (stepStart + stepSize > t)) ||
          ((! forward) && (stepStart + stepSize < t))) {
        stepSize = t - stepStart;
      }
      final double nextT = stepStart + stepSize;
      isLastStep = forward ? (nextT >= t) : (nextT <= t);

      // iterate over several substep sizes
      int k = -1;
      for (boolean loop = true; loop; ) {

        ++k;

        // modified midpoint integration with the current substep
        if ( ! tryStep(stepStart, y, stepSize, k, scale, fk[k],
                       (k == 0) ? yMidDots[0] : diagonal[k-1],
                       (k == 0) ? y1 : y1Diag[k-1],
                       yTmp)) {

          // the stability check failed, we reduce the global step
          hNew   = FastMath.abs(filterStep(stepSize * stabilityReduction, forward, false));
          reject = true;
          loop   = false;

        } else {

          // the substep was computed successfully
          if (k > 0) {

            // extrapolate the state at the end of the step
            // using last iteration data
            extrapolate(0, k, y1Diag, y1);
            rescale(y, y1, scale);

            // estimate the error at the end of the step.
            error = 0;
            for (int j = 0; j < mainSetDimension; ++j) {
              final double e = FastMath.abs(y1[j] - y1Diag[0][j]) / scale[j];
              error += e * e;
            }
            error = FastMath.sqrt(error / mainSetDimension);

            if ((error > 1.0e15) || ((k > 1) && (error > maxError))) {
              // error is too big, we reduce the global step
              hNew   = FastMath.abs(filterStep(stepSize * stabilityReduction, forward, false));
              reject = true;
              loop   = false;
            } else {

              maxError = FastMath.max(4 * error, 1.0);

              // compute optimal stepsize for this order
              final double exp = 1.0 / (2 * k + 1);
              double fac = stepControl2 / FastMath.pow(error / stepControl1, exp);
              final double pow = FastMath.pow(stepControl3, exp);
              fac = FastMath.max(pow / stepControl4, FastMath.min(1 / pow, fac));
              optimalStep[k]     = FastMath.abs(filterStep(stepSize * fac, forward, true));
              costPerTimeUnit[k] = costPerStep[k] / optimalStep[k];

              // check convergence
              switch (k - targetIter) {

              case -1 :
                if ((targetIter > 1) && ! previousRejected) {

                  // check if we can stop iterations now
                  if (error <= 1.0) {
                    // convergence have been reached just before targetIter
                    loop = false;
                  } else {
                    // estimate if there is a chance convergence will
                    // be reached on next iteration, using the
                    // asymptotic evolution of error
                    final double ratio = ((double) sequence [targetIter] * sequence[targetIter + 1]) /
                                         (sequence[0] * sequence[0]);
                    if (error > ratio * ratio) {
                      // we don't expect to converge on next iteration
                      // we reject the step immediately and reduce order
                      reject = true;
                      loop   = false;
                      targetIter = k;
                      if ((targetIter > 1) &&
                          (costPerTimeUnit[targetIter-1] <
                           orderControl1 * costPerTimeUnit[targetIter])) {
                        --targetIter;
                      }
                      hNew = optimalStep[targetIter];
                    }
                  }
                }
                break;

              case 0:
                if (error <= 1.0) {
                  // convergence has been reached exactly at targetIter
                  loop = false;
                } else {
                  // estimate if there is a chance convergence will
                  // be reached on next iteration, using the
                  // asymptotic evolution of error
                  final double ratio = ((double) sequence[k+1]) / sequence[0];
                  if (error > ratio * ratio) {
                    // we don't expect to converge on next iteration
                    // we reject the step immediately
                    reject = true;
                    loop = false;
                    if ((targetIter > 1) &&
                        (costPerTimeUnit[targetIter-1] <
                         orderControl1 * costPerTimeUnit[targetIter])) {
                      --targetIter;
                    }
                    hNew = optimalStep[targetIter];
                  }
                }
                break;

              case 1 :
                if (error > 1.0) {
                  reject = true;
                  if ((targetIter > 1) &&
                      (costPerTimeUnit[targetIter-1] <
                       orderControl1 * costPerTimeUnit[targetIter])) {
                    --targetIter;
                  }
                  hNew = optimalStep[targetIter];
                }
                loop = false;
                break;

              default :
                if ((firstTime || isLastStep) && (error <= 1.0)) {
                  loop = false;
                }
                break;

              }

            }
          }
        }
      }

      if (! reject) {
          // derivatives at end of step
          computeDerivatives(stepStart + stepSize, y1, yDot1);
      }

      // dense output handling
      double hInt = getMaxStep();
      if (! reject) {

        // extrapolate state at middle point of the step
        for (int j = 1; j <= k; ++j) {
          extrapolate(0, j, diagonal, yMidDots[0]);
        }

        final int mu = 2 * k - mudif + 3;

        for (int l = 0; l < mu; ++l) {

          // derivative at middle point of the step
          final int l2 = l / 2;
          double factor = FastMath.pow(0.5 * sequence[l2], l);
          int middleIndex = fk[l2].length / 2;
          for (int i = 0; i < y0.length; ++i) {
            yMidDots[l+1][i] = factor * fk[l2][middleIndex + l][i];
          }
          for (int j = 1; j <= k - l2; ++j) {
            factor = FastMath.pow(0.5 * sequence[j + l2], l);
            middleIndex = fk[l2+j].length / 2;
            for (int i = 0; i < y0.length; ++i) {
              diagonal[j-1][i] = factor * fk[l2+j][middleIndex+l][i];
            }
            extrapolate(l2, j, diagonal, yMidDots[l+1]);
          }
          for (int i = 0; i < y0.length; ++i) {
            yMidDots[l+1][i] *= stepSize;
          }

          // compute centered differences to evaluate next derivatives
          for (int j = (l + 1) / 2; j <= k; ++j) {
            for (int m = fk[j].length - 1; m >= 2 * (l + 1); --m) {
              for (int i = 0; i < y0.length; ++i) {
                fk[j][m][i] -= fk[j][m-2][i];
              }
            }
          }

        }

        if (mu >= 0) {

          // estimate the dense output coefficients
          final GraggBulirschStoerStepInterpolator gbsInterpolator
            = (GraggBulirschStoerStepInterpolator) interpolator;
          gbsInterpolator.computeCoefficients(mu, stepSize);

          if (useInterpolationError) {
            // use the interpolation error to limit stepsize
            final double interpError = gbsInterpolator.estimateError(scale);
            hInt = FastMath.abs(stepSize / FastMath.max(FastMath.pow(interpError, 1.0 / (mu+4)),
                                                0.01));
            if (interpError > 10.0) {
              hNew = hInt;
              reject = true;
            }
          }

        }

      }

      if (! reject) {

        // Discrete events handling
        interpolator.storeTime(stepStart + stepSize);
        stepStart = acceptStep(interpolator, y1, yDot1, t);

        // prepare next step
        interpolator.storeTime(stepStart);
        System.arraycopy(y1, 0, y, 0, y0.length);
        System.arraycopy(yDot1, 0, yDot0, 0, y0.length);
        firstStepAlreadyComputed = true;

        int optimalIter;
        if (k == 1) {
          optimalIter = 2;
          if (previousRejected) {
            optimalIter = 1;
          }
        } else if (k <= targetIter) {
          optimalIter = k;
          if (costPerTimeUnit[k-1] < orderControl1 * costPerTimeUnit[k]) {
            optimalIter = k-1;
          } else if (costPerTimeUnit[k] < orderControl2 * costPerTimeUnit[k-1]) {
            optimalIter = FastMath.min(k+1, sequence.length - 2);
          }
        } else {
          optimalIter = k - 1;
          if ((k > 2) &&
              (costPerTimeUnit[k-2] < orderControl1 * costPerTimeUnit[k-1])) {
            optimalIter = k - 2;
          }
          if (costPerTimeUnit[k] < orderControl2 * costPerTimeUnit[optimalIter]) {
            optimalIter = FastMath.min(k, sequence.length - 2);
          }
        }

        if (previousRejected) {
          // after a rejected step neither order nor stepsize
          // should increase
          targetIter = FastMath.min(optimalIter, k);
          hNew = FastMath.min(FastMath.abs(stepSize), optimalStep[targetIter]);
        } else {
          // stepsize control
          if (optimalIter <= k) {
            hNew = optimalStep[optimalIter];
          } else {
            if ((k < targetIter) &&
                (costPerTimeUnit[k] < orderControl2 * costPerTimeUnit[k-1])) {
              hNew = filterStep(optimalStep[k] * costPerStep[optimalIter+1] / costPerStep[k],
                               forward, false);
            } else {
              hNew = filterStep(optimalStep[k] * costPerStep[optimalIter] / costPerStep[k],
                                forward, false);
            }
          }

          targetIter = optimalIter;

        }

        newStep = true;

      }

      hNew = FastMath.min(hNew, hInt);
      if (! forward) {
        hNew = -hNew;
      }

      firstTime = false;

      if (reject) {
        isLastStep = false;
        previousRejected = true;
      } else {
        previousRejected = false;
      }

    } while (!isLastStep);

    // dispatch results
    equations.setTime(stepStart);
    equations.setCompleteState(y);

    resetInternalState();

  }

}
