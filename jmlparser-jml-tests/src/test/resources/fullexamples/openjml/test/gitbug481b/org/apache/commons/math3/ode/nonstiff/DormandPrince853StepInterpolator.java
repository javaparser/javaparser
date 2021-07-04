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

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;

import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.ode.AbstractIntegrator;
import org.apache.commons.math3.ode.EquationsMapper;
import org.apache.commons.math3.ode.sampling.StepInterpolator;

/**
 * This class represents an interpolator over the last step during an
 * ODE integration for the 8(5,3) Dormand-Prince integrator.
 *
 * @see DormandPrince853Integrator
 *
 * @since 1.2
 */

class DormandPrince853StepInterpolator
  extends RungeKuttaStepInterpolator {

    /** Serializable version identifier. */
    private static final long serialVersionUID = 20111120L;

    /** Propagation weights, element 1. */
    private static final double B_01 =         104257.0 / 1920240.0;

    // elements 2 to 5 are zero, so they are neither stored nor used

    /** Propagation weights, element 6. */
    private static final double B_06 =        3399327.0 / 763840.0;

    /** Propagation weights, element 7. */
    private static final double B_07 =       66578432.0 / 35198415.0;

    /** Propagation weights, element 8. */
    private static final double B_08 =    -1674902723.0 / 288716400.0;

    /** Propagation weights, element 9. */
    private static final double B_09 = 54980371265625.0 / 176692375811392.0;

    /** Propagation weights, element 10. */
    private static final double B_10 =        -734375.0 / 4826304.0;

    /** Propagation weights, element 11. */
    private static final double B_11 =      171414593.0 / 851261400.0;

    /** Propagation weights, element 12. */
    private static final double B_12 =         137909.0 / 3084480.0;

    /** Time step for stage 14 (interpolation only). */
    private static final double C14    = 1.0 / 10.0;

    /** Internal weights for stage 14, element 1. */
    private static final double K14_01 =       13481885573.0 / 240030000000.0      - B_01;

    // elements 2 to 5 are zero, so they are neither stored nor used

    /** Internal weights for stage 14, element 6. */
    private static final double K14_06 =                 0.0                       - B_06;

    /** Internal weights for stage 14, element 7. */
    private static final double K14_07 =      139418837528.0 / 549975234375.0      - B_07;

    /** Internal weights for stage 14, element 8. */
    private static final double K14_08 =   -11108320068443.0 / 45111937500000.0    - B_08;

    /** Internal weights for stage 14, element 9. */
    private static final double K14_09 = -1769651421925959.0 / 14249385146080000.0 - B_09;

    /** Internal weights for stage 14, element 10. */
    private static final double K14_10 =          57799439.0 / 377055000.0         - B_10;

    /** Internal weights for stage 14, element 11. */
    private static final double K14_11 =      793322643029.0 / 96734250000000.0    - B_11;

    /** Internal weights for stage 14, element 12. */
    private static final double K14_12 =        1458939311.0 / 192780000000.0      - B_12;

    /** Internal weights for stage 14, element 13. */
    private static final double K14_13 =             -4149.0 / 500000.0;

    /** Time step for stage 15 (interpolation only). */
    private static final double C15    = 1.0 / 5.0;


    /** Internal weights for stage 15, element 1. */
    private static final double K15_01 =     1595561272731.0 / 50120273500000.0    - B_01;

    // elements 2 to 5 are zero, so they are neither stored nor used

    /** Internal weights for stage 15, element 6. */
    private static final double K15_06 =      975183916491.0 / 34457688031250.0    - B_06;

    /** Internal weights for stage 15, element 7. */
    private static final double K15_07 =    38492013932672.0 / 718912673015625.0   - B_07;

    /** Internal weights for stage 15, element 8. */
    private static final double K15_08 = -1114881286517557.0 / 20298710767500000.0 - B_08;

    /** Internal weights for stage 15, element 9. */
    private static final double K15_09 =                 0.0                       - B_09;

    /** Internal weights for stage 15, element 10. */
    private static final double K15_10 =                 0.0                       - B_10;

    /** Internal weights for stage 15, element 11. */
    private static final double K15_11 =    -2538710946863.0 / 23431227861250000.0 - B_11;

    /** Internal weights for stage 15, element 12. */
    private static final double K15_12 =        8824659001.0 / 23066716781250.0    - B_12;

    /** Internal weights for stage 15, element 13. */
    private static final double K15_13 =      -11518334563.0 / 33831184612500.0;

    /** Internal weights for stage 15, element 14. */
    private static final double K15_14 =        1912306948.0 / 13532473845.0;

    /** Time step for stage 16 (interpolation only). */
    private static final double C16    = 7.0 / 9.0;


    /** Internal weights for stage 16, element 1. */
    private static final double K16_01 =      -13613986967.0 / 31741908048.0       - B_01;

    // elements 2 to 5 are zero, so they are neither stored nor used

    /** Internal weights for stage 16, element 6. */
    private static final double K16_06 =       -4755612631.0 / 1012344804.0        - B_06;

    /** Internal weights for stage 16, element 7. */
    private static final double K16_07 =    42939257944576.0 / 5588559685701.0     - B_07;

    /** Internal weights for stage 16, element 8. */
    private static final double K16_08 =    77881972900277.0 / 19140370552944.0    - B_08;

    /** Internal weights for stage 16, element 9. */
    private static final double K16_09 =    22719829234375.0 / 63689648654052.0    - B_09;

    /** Internal weights for stage 16, element 10. */
    private static final double K16_10 =                 0.0                       - B_10;

    /** Internal weights for stage 16, element 11. */
    private static final double K16_11 =                 0.0                       - B_11;

    /** Internal weights for stage 16, element 12. */
    private static final double K16_12 =                 0.0                       - B_12;

    /** Internal weights for stage 16, element 13. */
    private static final double K16_13 =       -1199007803.0 / 857031517296.0;

    /** Internal weights for stage 16, element 14. */
    private static final double K16_14 =      157882067000.0 / 53564469831.0;

    /** Internal weights for stage 16, element 15. */
    private static final double K16_15 =     -290468882375.0 / 31741908048.0;

    /** Interpolation weights.
     * (beware that only the non-null values are in the table)
     */
    private static final double[][] D = {

      {        -17751989329.0 / 2106076560.0,               4272954039.0 / 7539864640.0,
              -118476319744.0 / 38604839385.0,            755123450731.0 / 316657731600.0,
        3692384461234828125.0 / 1744130441634250432.0,     -4612609375.0 / 5293382976.0,
              2091772278379.0 / 933644586600.0,             2136624137.0 / 3382989120.0,
                    -126493.0 / 1421424.0,                    98350000.0 / 5419179.0,
                  -18878125.0 / 2053168.0,                 -1944542619.0 / 438351368.0},

      {         32941697297.0 / 3159114840.0,             456696183123.0 / 1884966160.0,
             19132610714624.0 / 115814518155.0,       -177904688592943.0 / 474986597400.0,
       -4821139941836765625.0 / 218016305204281304.0,      30702015625.0 / 3970037232.0,
            -85916079474274.0 / 2800933759800.0,           -5919468007.0 / 634310460.0,
                    2479159.0 / 157936.0,                    -18750000.0 / 602131.0,
                  -19203125.0 / 2053168.0,                 15700361463.0 / 438351368.0},

      {         12627015655.0 / 631822968.0,              -72955222965.0 / 188496616.0,
            -13145744952320.0 / 69488710893.0,          30084216194513.0 / 56998391688.0,
        -296858761006640625.0 / 25648977082856624.0,         569140625.0 / 82709109.0,
               -18684190637.0 / 18672891732.0,                69644045.0 / 89549712.0,
                  -11847025.0 / 4264272.0,                  -978650000.0 / 16257537.0,
                  519371875.0 / 6159504.0,                  5256837225.0 / 438351368.0},

      {          -450944925.0 / 17550638.0,               -14532122925.0 / 94248308.0,
              -595876966400.0 / 2573655959.0,             188748653015.0 / 527762886.0,
        2545485458115234375.0 / 27252038150535163.0,       -1376953125.0 / 36759604.0,
                53995596795.0 / 518691437.0,                 210311225.0 / 7047894.0,
                   -1718875.0 / 39484.0,                      58000000.0 / 602131.0,
                   -1546875.0 / 39484.0,                   -1262172375.0 / 8429834.0}

    };

    /** Last evaluations. */
    private double[][] yDotKLast;

    /** Vectors for interpolation. */
    private double[][] v;

    /** Initialization indicator for the interpolation vectors. */
    private boolean vectorsInitialized;

  /** Simple constructor.
   * This constructor builds an instance that is not usable yet, the
   * {@link #reinitialize} method should be called before using the
   * instance in order to initialize the internal arrays. This
   * constructor is used only in order to delay the initialization in
   * some cases. The {@link EmbeddedRungeKuttaIntegrator} uses the
   * prototyping design pattern to create the step interpolators by
   * cloning an uninitialized model and latter initializing the copy.
   */
  // CHECKSTYLE: stop RedundantModifier
  // the public modifier here is needed for serialization
  public DormandPrince853StepInterpolator() {
    super();
    yDotKLast = null;
    v         = null;
    vectorsInitialized = false;
  }
  // CHECKSTYLE: resume RedundantModifier

  /** Copy constructor.
   * @param interpolator interpolator to copy from. The copy is a deep
   * copy: its arrays are separated from the original arrays of the
   * instance
   */
  DormandPrince853StepInterpolator(final DormandPrince853StepInterpolator interpolator) {

    super(interpolator);

    if (interpolator.currentState == null) {

      yDotKLast = null;
      v         = null;
      vectorsInitialized = false;

    } else {

      final int dimension = interpolator.currentState.length;

      yDotKLast    = new double[3][];
      for (int k = 0; k < yDotKLast.length; ++k) {
        yDotKLast[k] = new double[dimension];
        System.arraycopy(interpolator.yDotKLast[k], 0, yDotKLast[k], 0,
                         dimension);
      }

      v = new double[7][];
      for (int k = 0; k < v.length; ++k) {
        v[k] = new double[dimension];
        System.arraycopy(interpolator.v[k], 0, v[k], 0, dimension);
      }

      vectorsInitialized = interpolator.vectorsInitialized;

    }

  }

  /** {@inheritDoc} */
  @Override
  protected StepInterpolator doCopy() {
    return new DormandPrince853StepInterpolator(this);
  }

  /** {@inheritDoc} */
  @Override
  public void reinitialize(final AbstractIntegrator integrator,
                           final double[] y, final double[][] yDotK, final boolean forward,
                           final EquationsMapper primaryMapper,
                           final EquationsMapper[] secondaryMappers) {

    super.reinitialize(integrator, y, yDotK, forward, primaryMapper, secondaryMappers);

    final int dimension = currentState.length;

    yDotKLast = new double[3][];
    for (int k = 0; k < yDotKLast.length; ++k) {
      yDotKLast[k] = new double[dimension];
    }

    v = new double[7][];
    for (int k = 0; k < v.length; ++k) {
      v[k]  = new double[dimension];
    }

    vectorsInitialized = false;

  }

  /** {@inheritDoc} */
  @Override
  public void storeTime(final double t) {
    super.storeTime(t);
    vectorsInitialized = false;
  }

  /** {@inheritDoc} */
  @Override
  protected void computeInterpolatedStateAndDerivatives(final double theta,
                                          final double oneMinusThetaH)
      throws MaxCountExceededException {

    if (! vectorsInitialized) {

      if (v == null) {
        v = new double[7][];
        for (int k = 0; k < 7; ++k) {
          v[k] = new double[interpolatedState.length];
        }
      }

      // perform the last evaluations if they have not been done yet
      finalizeStep();

      // compute the interpolation vectors for this time step
      for (int i = 0; i < interpolatedState.length; ++i) {
          final double yDot1  = yDotK[0][i];
          final double yDot6  = yDotK[5][i];
          final double yDot7  = yDotK[6][i];
          final double yDot8  = yDotK[7][i];
          final double yDot9  = yDotK[8][i];
          final double yDot10 = yDotK[9][i];
          final double yDot11 = yDotK[10][i];
          final double yDot12 = yDotK[11][i];
          final double yDot13 = yDotK[12][i];
          final double yDot14 = yDotKLast[0][i];
          final double yDot15 = yDotKLast[1][i];
          final double yDot16 = yDotKLast[2][i];
          v[0][i] = B_01 * yDot1  + B_06 * yDot6 + B_07 * yDot7 +
                    B_08 * yDot8  + B_09 * yDot9 + B_10 * yDot10 +
                    B_11 * yDot11 + B_12 * yDot12;
          v[1][i] = yDot1 - v[0][i];
          v[2][i] = v[0][i] - v[1][i] - yDotK[12][i];
          for (int k = 0; k < D.length; ++k) {
              v[k+3][i] = D[k][0] * yDot1  + D[k][1]  * yDot6  + D[k][2]  * yDot7  +
                          D[k][3] * yDot8  + D[k][4]  * yDot9  + D[k][5]  * yDot10 +
                          D[k][6] * yDot11 + D[k][7]  * yDot12 + D[k][8]  * yDot13 +
                          D[k][9] * yDot14 + D[k][10] * yDot15 + D[k][11] * yDot16;
          }
      }

      vectorsInitialized = true;

    }

    final double eta      = 1 - theta;
    final double twoTheta = 2 * theta;
    final double theta2   = theta * theta;
    final double dot1 = 1 - twoTheta;
    final double dot2 = theta * (2 - 3 * theta);
    final double dot3 = twoTheta * (1 + theta * (twoTheta -3));
    final double dot4 = theta2 * (3 + theta * (5 * theta - 8));
    final double dot5 = theta2 * (3 + theta * (-12 + theta * (15 - 6 * theta)));
    final double dot6 = theta2 * theta * (4 + theta * (-15 + theta * (18 - 7 * theta)));

    if ((previousState != null) && (theta <= 0.5)) {
        for (int i = 0; i < interpolatedState.length; ++i) {
            interpolatedState[i] = previousState[i] +
                    theta * h * (v[0][i] +
                            eta * (v[1][i] +
                                    theta * (v[2][i] +
                                            eta * (v[3][i] +
                                                    theta * (v[4][i] +
                                                            eta * (v[5][i] +
                                                                    theta * (v[6][i])))))));
            interpolatedDerivatives[i] =  v[0][i] + dot1 * v[1][i] + dot2 * v[2][i] +
                    dot3 * v[3][i] + dot4 * v[4][i] +
                    dot5 * v[5][i] + dot6 * v[6][i];
        }
    } else {
        for (int i = 0; i < interpolatedState.length; ++i) {
            interpolatedState[i] = currentState[i] -
                    oneMinusThetaH * (v[0][i] -
                            theta * (v[1][i] +
                                    theta * (v[2][i] +
                                            eta * (v[3][i] +
                                                    theta * (v[4][i] +
                                                            eta * (v[5][i] +
                                                                    theta * (v[6][i])))))));
            interpolatedDerivatives[i] =  v[0][i] + dot1 * v[1][i] + dot2 * v[2][i] +
                    dot3 * v[3][i] + dot4 * v[4][i] +
                    dot5 * v[5][i] + dot6 * v[6][i];
        }
    }

  }

  /** {@inheritDoc} */
  @Override
  protected void doFinalize() throws MaxCountExceededException {

      if (currentState == null) {
          // we are finalizing an uninitialized instance
          return;
      }

      double s;
      final double[] yTmp = new double[currentState.length];
      final double pT = getGlobalPreviousTime();

      // k14
      for (int j = 0; j < currentState.length; ++j) {
          s = K14_01 * yDotK[0][j]  + K14_06 * yDotK[5][j]  + K14_07 * yDotK[6][j] +
                  K14_08 * yDotK[7][j]  + K14_09 * yDotK[8][j]  + K14_10 * yDotK[9][j] +
                  K14_11 * yDotK[10][j] + K14_12 * yDotK[11][j] + K14_13 * yDotK[12][j];
          yTmp[j] = currentState[j] + h * s;
      }
      integrator.computeDerivatives(pT + C14 * h, yTmp, yDotKLast[0]);

      // k15
      for (int j = 0; j < currentState.length; ++j) {
          s = K15_01 * yDotK[0][j]  + K15_06 * yDotK[5][j]  + K15_07 * yDotK[6][j] +
                  K15_08 * yDotK[7][j]  + K15_09 * yDotK[8][j]  + K15_10 * yDotK[9][j] +
                  K15_11 * yDotK[10][j] + K15_12 * yDotK[11][j] + K15_13 * yDotK[12][j] +
                  K15_14 * yDotKLast[0][j];
          yTmp[j] = currentState[j] + h * s;
      }
      integrator.computeDerivatives(pT + C15 * h, yTmp, yDotKLast[1]);

      // k16
      for (int j = 0; j < currentState.length; ++j) {
          s = K16_01 * yDotK[0][j]  + K16_06 * yDotK[5][j]  + K16_07 * yDotK[6][j] +
                  K16_08 * yDotK[7][j]  + K16_09 * yDotK[8][j]  + K16_10 * yDotK[9][j] +
                  K16_11 * yDotK[10][j] + K16_12 * yDotK[11][j] + K16_13 * yDotK[12][j] +
                  K16_14 * yDotKLast[0][j] +  K16_15 * yDotKLast[1][j];
          yTmp[j] = currentState[j] + h * s;
      }
      integrator.computeDerivatives(pT + C16 * h, yTmp, yDotKLast[2]);

  }

  /** {@inheritDoc} */
  @Override
  public void writeExternal(final ObjectOutput out)
    throws IOException {

    try {
        // save the local attributes
        finalizeStep();
    } catch (MaxCountExceededException mcee) {
        final IOException ioe = new IOException(mcee.getLocalizedMessage());
        ioe.initCause(mcee);
        throw ioe;
    }

    final int dimension = (currentState == null) ? -1 : currentState.length;
    out.writeInt(dimension);
    for (int i = 0; i < dimension; ++i) {
      out.writeDouble(yDotKLast[0][i]);
      out.writeDouble(yDotKLast[1][i]);
      out.writeDouble(yDotKLast[2][i]);
    }

    // save the state of the base class
    super.writeExternal(out);

  }

  /** {@inheritDoc} */
  @Override
  public void readExternal(final ObjectInput in)
    throws IOException, ClassNotFoundException {

    // read the local attributes
    yDotKLast = new double[3][];
    final int dimension = in.readInt();
    yDotKLast[0] = (dimension < 0) ? null : new double[dimension];
    yDotKLast[1] = (dimension < 0) ? null : new double[dimension];
    yDotKLast[2] = (dimension < 0) ? null : new double[dimension];

    for (int i = 0; i < dimension; ++i) {
      yDotKLast[0][i] = in.readDouble();
      yDotKLast[1][i] = in.readDouble();
      yDotKLast[2][i] = in.readDouble();
    }

    // read the base state
    super.readExternal(in);

  }

}
