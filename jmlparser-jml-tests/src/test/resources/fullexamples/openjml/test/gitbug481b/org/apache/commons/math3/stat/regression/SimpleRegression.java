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

package org.apache.commons.math3.stat.regression;
import java.io.Serializable;

import org.apache.commons.math3.distribution.TDistribution;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Precision;

/**
 * Estimates an ordinary least squares regression model
 * with one independent variable.
 * <p>
 * <code> y = intercept + slope * x  </code></p>
 * <p>
 * Standard errors for <code>intercept</code> and <code>slope</code> are
 * available as well as ANOVA, r-square and Pearson's r statistics.</p>
 * <p>
 * Observations (x,y pairs) can be added to the model one at a time or they
 * can be provided in a 2-dimensional array.  The observations are not stored
 * in memory, so there is no limit to the number of observations that can be
 * added to the model.</p>
 * <p>
 * <strong>Usage Notes</strong>: <ul>
 * <li> When there are fewer than two observations in the model, or when
 * there is no variation in the x values (i.e. all x values are the same)
 * all statistics return <code>NaN</code>. At least two observations with
 * different x coordinates are required to estimate a bivariate regression
 * model.
 * </li>
 * <li> Getters for the statistics always compute values based on the current
 * set of observations -- i.e., you can get statistics, then add more data
 * and get updated statistics without using a new instance.  There is no
 * "compute" method that updates all statistics.  Each of the getters performs
 * the necessary computations to return the requested statistic.
 * </li>
 * <li> The intercept term may be suppressed by passing {@code false} to
 * the {@link #SimpleRegression(boolean)} constructor.  When the
 * {@code hasIntercept} property is false, the model is estimated without a
 * constant term and {@link #getIntercept()} returns {@code 0}.</li>
 * </ul></p>
 *
 */
public class SimpleRegression implements Serializable, UpdatingMultipleLinearRegression {

    /** Serializable version identifier */
    private static final long serialVersionUID = -3004689053607543335L;

    /** sum of x values */
    private double sumX = 0d;

    /** total variation in x (sum of squared deviations from xbar) */
    private double sumXX = 0d;

    /** sum of y values */
    private double sumY = 0d;

    /** total variation in y (sum of squared deviations from ybar) */
    private double sumYY = 0d;

    /** sum of products */
    private double sumXY = 0d;

    /** number of observations */
    private long n = 0;

    /** mean of accumulated x values, used in updating formulas */
    private double xbar = 0;

    /** mean of accumulated y values, used in updating formulas */
    private double ybar = 0;

    /** include an intercept or not */
    private final boolean hasIntercept;
    // ---------------------Public methods--------------------------------------

    /**
     * Create an empty SimpleRegression instance
     */
    public SimpleRegression() {
        this(true);
    }
    /**
    * Create a SimpleRegression instance, specifying whether or not to estimate
    * an intercept.
    *
    * <p>Use {@code false} to estimate a model with no intercept.  When the
    * {@code hasIntercept} property is false, the model is estimated without a
    * constant term and {@link #getIntercept()} returns {@code 0}.</p>
    *
    * @param includeIntercept whether or not to include an intercept term in
    * the regression model
    */
    public SimpleRegression(boolean includeIntercept) {
        super();
        hasIntercept = includeIntercept;
    }

    /**
     * Adds the observation (x,y) to the regression data set.
     * <p>
     * Uses updating formulas for means and sums of squares defined in
     * "Algorithms for Computing the Sample Variance: Analysis and
     * Recommendations", Chan, T.F., Golub, G.H., and LeVeque, R.J.
     * 1983, American Statistician, vol. 37, pp. 242-247, referenced in
     * Weisberg, S. "Applied Linear Regression". 2nd Ed. 1985.</p>
     *
     *
     * @param x independent variable value
     * @param y dependent variable value
     */
    public void addData(final double x,final double y) {
        if (n == 0) {
            xbar = x;
            ybar = y;
        } else {
            if( hasIntercept ){
                final double fact1 = 1.0 + n;
                final double fact2 = n / (1.0 + n);
                final double dx = x - xbar;
                final double dy = y - ybar;
                sumXX += dx * dx * fact2;
                sumYY += dy * dy * fact2;
                sumXY += dx * dy * fact2;
                xbar += dx / fact1;
                ybar += dy / fact1;
            }
         }
        if( !hasIntercept ){
            sumXX += x * x ;
            sumYY += y * y ;
            sumXY += x * y ;
        }
        sumX += x;
        sumY += y;
        n++;
    }

    /**
     * Appends data from another regression calculation to this one.
     *
     * <p>The mean update formulae are based on a paper written by Philippe
     * P&eacute;bay:
     * <a
     * href="http://prod.sandia.gov/techlib/access-control.cgi/2008/086212.pdf">
     * Formulas for Robust, One-Pass Parallel Computation of Covariances and
     * Arbitrary-Order Statistical Moments</a>, 2008, Technical Report
     * SAND2008-6212, Sandia National Laboratories.</p>
     *
     * @param reg model to append data from
     * @since 3.3
     */
    public void append(SimpleRegression reg) {
        if (n == 0) {
            xbar = reg.xbar;
            ybar = reg.ybar;
            sumXX = reg.sumXX;
            sumYY = reg.sumYY;
            sumXY = reg.sumXY;
        } else {
            if (hasIntercept) {
                final double fact1 = reg.n / (double) (reg.n + n);
                final double fact2 = n * reg.n / (double) (reg.n + n);
                final double dx = reg.xbar - xbar;
                final double dy = reg.ybar - ybar;
                sumXX += reg.sumXX + dx * dx * fact2;
                sumYY += reg.sumYY + dy * dy * fact2;
                sumXY += reg.sumXY + dx * dy * fact2;
                xbar += dx * fact1;
                ybar += dy * fact1;
            }else{
                sumXX += reg.sumXX;
                sumYY += reg.sumYY;
                sumXY += reg.sumXY;
            }
        }
        sumX += reg.sumX;
        sumY += reg.sumY;
        n += reg.n;
    }

    /**
     * Removes the observation (x,y) from the regression data set.
     * <p>
     * Mirrors the addData method.  This method permits the use of
     * SimpleRegression instances in streaming mode where the regression
     * is applied to a sliding "window" of observations, however the caller is
     * responsible for maintaining the set of observations in the window.</p>
     *
     * The method has no effect if there are no points of data (i.e. n=0)
     *
     * @param x independent variable value
     * @param y dependent variable value
     */
    public void removeData(final double x,final double y) {
        if (n > 0) {
            if (hasIntercept) {
                final double fact1 = n - 1.0;
                final double fact2 = n / (n - 1.0);
                final double dx = x - xbar;
                final double dy = y - ybar;
                sumXX -= dx * dx * fact2;
                sumYY -= dy * dy * fact2;
                sumXY -= dx * dy * fact2;
                xbar -= dx / fact1;
                ybar -= dy / fact1;
            } else {
                final double fact1 = n - 1.0;
                sumXX -= x * x;
                sumYY -= y * y;
                sumXY -= x * y;
                xbar -= x / fact1;
                ybar -= y / fact1;
            }
             sumX -= x;
             sumY -= y;
             n--;
        }
    }

    /**
     * Adds the observations represented by the elements in
     * <code>data</code>.
     * <p>
     * <code>(data[0][0],data[0][1])</code> will be the first observation, then
     * <code>(data[1][0],data[1][1])</code>, etc.</p>
     * <p>
     * This method does not replace data that has already been added.  The
     * observations represented by <code>data</code> are added to the existing
     * dataset.</p>
     * <p>
     * To replace all data, use <code>clear()</code> before adding the new
     * data.</p>
     *
     * @param data array of observations to be added
     * @throws ModelSpecificationException if the length of {@code data[i]} is not
     * greater than or equal to 2
     */
    public void addData(final double[][] data) throws ModelSpecificationException {
        for (int i = 0; i < data.length; i++) {
            if( data[i].length < 2 ){
               throw new ModelSpecificationException(LocalizedFormats.INVALID_REGRESSION_OBSERVATION,
                    data[i].length, 2);
            }
            addData(data[i][0], data[i][1]);
        }
    }

    /**
     * Adds one observation to the regression model.
     *
     * @param x the independent variables which form the design matrix
     * @param y the dependent or response variable
     * @throws ModelSpecificationException if the length of {@code x} does not equal
     * the number of independent variables in the model
     */
    public void addObservation(final double[] x,final double y)
    throws ModelSpecificationException {
        if( x == null || x.length == 0 ){
            throw new ModelSpecificationException(LocalizedFormats.INVALID_REGRESSION_OBSERVATION,x!=null?x.length:0, 1);
        }
        addData( x[0], y );
    }

    /**
     * Adds a series of observations to the regression model. The lengths of
     * x and y must be the same and x must be rectangular.
     *
     * @param x a series of observations on the independent variables
     * @param y a series of observations on the dependent variable
     * The length of x and y must be the same
     * @throws ModelSpecificationException if {@code x} is not rectangular, does not match
     * the length of {@code y} or does not contain sufficient data to estimate the model
     */
    public void addObservations(final double[][] x,final double[] y) throws ModelSpecificationException {
        if ((x == null) || (y == null) || (x.length != y.length)) {
            throw new ModelSpecificationException(
                  LocalizedFormats.DIMENSIONS_MISMATCH_SIMPLE,
                  (x == null) ? 0 : x.length,
                  (y == null) ? 0 : y.length);
        }
        boolean obsOk=true;
        for( int i = 0 ; i < x.length; i++){
            if( x[i] == null || x[i].length == 0 ){
                obsOk = false;
            }
        }
        if( !obsOk ){
            throw new ModelSpecificationException(
                  LocalizedFormats.NOT_ENOUGH_DATA_FOR_NUMBER_OF_PREDICTORS,
                  0, 1);
        }
        for( int i = 0 ; i < x.length ; i++){
            addData( x[i][0], y[i] );
        }
    }

    /**
     * Removes observations represented by the elements in <code>data</code>.
      * <p>
     * If the array is larger than the current n, only the first n elements are
     * processed.  This method permits the use of SimpleRegression instances in
     * streaming mode where the regression is applied to a sliding "window" of
     * observations, however the caller is responsible for maintaining the set
     * of observations in the window.</p>
     * <p>
     * To remove all data, use <code>clear()</code>.</p>
     *
     * @param data array of observations to be removed
     */
    public void removeData(double[][] data) {
        for (int i = 0; i < data.length && n > 0; i++) {
            removeData(data[i][0], data[i][1]);
        }
    }

    /**
     * Clears all data from the model.
     */
    public void clear() {
        sumX = 0d;
        sumXX = 0d;
        sumY = 0d;
        sumYY = 0d;
        sumXY = 0d;
        n = 0;
    }

    /**
     * Returns the number of observations that have been added to the model.
     *
     * @return n number of observations that have been added.
     */
    public long getN() {
        return n;
    }

    /**
     * Returns the "predicted" <code>y</code> value associated with the
     * supplied <code>x</code> value,  based on the data that has been
     * added to the model when this method is activated.
     * <p>
     * <code> predict(x) = intercept + slope * x </code></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>At least two observations (with at least two different x values)
     * must have been added before invoking this method. If this method is
     * invoked before a model can be estimated, <code>Double,NaN</code> is
     * returned.
     * </li></ul></p>
     *
     * @param x input <code>x</code> value
     * @return predicted <code>y</code> value
     */
    public double predict(final double x) {
        final double b1 = getSlope();
        if (hasIntercept) {
            return getIntercept(b1) + b1 * x;
        }
        return b1 * x;
    }

    /**
     * Returns the intercept of the estimated regression line, if
     * {@link #hasIntercept()} is true; otherwise 0.
     * <p>
     * The least squares estimate of the intercept is computed using the
     * <a href="http://www.xycoon.com/estimation4.htm">normal equations</a>.
     * The intercept is sometimes denoted b0.</p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>At least two observations (with at least two different x values)
     * must have been added before invoking this method. If this method is
     * invoked before a model can be estimated, <code>Double,NaN</code> is
     * returned.
     * </li></ul></p>
     *
     * @return the intercept of the regression line if the model includes an
     * intercept; 0 otherwise
     * @see #SimpleRegression(boolean)
     */
    public double getIntercept() {
        return hasIntercept ? getIntercept(getSlope()) : 0.0;
    }

    /**
     * Returns true if the model includes an intercept term.
     *
     * @return true if the regression includes an intercept; false otherwise
     * @see #SimpleRegression(boolean)
     */
    public boolean hasIntercept() {
        return hasIntercept;
    }

    /**
    * Returns the slope of the estimated regression line.
    * <p>
    * The least squares estimate of the slope is computed using the
    * <a href="http://www.xycoon.com/estimation4.htm">normal equations</a>.
    * The slope is sometimes denoted b1.</p>
    * <p>
    * <strong>Preconditions</strong>: <ul>
    * <li>At least two observations (with at least two different x values)
    * must have been added before invoking this method. If this method is
    * invoked before a model can be estimated, <code>Double.NaN</code> is
    * returned.
    * </li></ul></p>
    *
    * @return the slope of the regression line
    */
    public double getSlope() {
        if (n < 2) {
            return Double.NaN; //not enough data
        }
        if (FastMath.abs(sumXX) < 10 * Double.MIN_VALUE) {
            return Double.NaN; //not enough variation in x
        }
        return sumXY / sumXX;
    }

    /**
     * Returns the <a href="http://www.xycoon.com/SumOfSquares.htm">
     * sum of squared errors</a> (SSE) associated with the regression
     * model.
     * <p>
     * The sum is computed using the computational formula</p>
     * <p>
     * <code>SSE = SYY - (SXY * SXY / SXX)</code></p>
     * <p>
     * where <code>SYY</code> is the sum of the squared deviations of the y
     * values about their mean, <code>SXX</code> is similarly defined and
     * <code>SXY</code> is the sum of the products of x and y mean deviations.
     * </p><p>
     * The sums are accumulated using the updating algorithm referenced in
     * {@link #addData}.</p>
     * <p>
     * The return value is constrained to be non-negative - i.e., if due to
     * rounding errors the computational formula returns a negative result,
     * 0 is returned.</p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>At least two observations (with at least two different x values)
     * must have been added before invoking this method. If this method is
     * invoked before a model can be estimated, <code>Double,NaN</code> is
     * returned.
     * </li></ul></p>
     *
     * @return sum of squared errors associated with the regression model
     */
    public double getSumSquaredErrors() {
        return FastMath.max(0d, sumYY - sumXY * sumXY / sumXX);
    }

    /**
     * Returns the sum of squared deviations of the y values about their mean.
     * <p>
     * This is defined as SSTO
     * <a href="http://www.xycoon.com/SumOfSquares.htm">here</a>.</p>
     * <p>
     * If <code>n < 2</code>, this returns <code>Double.NaN</code>.</p>
     *
     * @return sum of squared deviations of y values
     */
    public double getTotalSumSquares() {
        if (n < 2) {
            return Double.NaN;
        }
        return sumYY;
    }

    /**
     * Returns the sum of squared deviations of the x values about their mean.
     *
     * If <code>n < 2</code>, this returns <code>Double.NaN</code>.</p>
     *
     * @return sum of squared deviations of x values
     */
    public double getXSumSquares() {
        if (n < 2) {
            return Double.NaN;
        }
        return sumXX;
    }

    /**
     * Returns the sum of crossproducts, x<sub>i</sub>*y<sub>i</sub>.
     *
     * @return sum of cross products
     */
    public double getSumOfCrossProducts() {
        return sumXY;
    }

    /**
     * Returns the sum of squared deviations of the predicted y values about
     * their mean (which equals the mean of y).
     * <p>
     * This is usually abbreviated SSR or SSM.  It is defined as SSM
     * <a href="http://www.xycoon.com/SumOfSquares.htm">here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>At least two observations (with at least two different x values)
     * must have been added before invoking this method. If this method is
     * invoked before a model can be estimated, <code>Double.NaN</code> is
     * returned.
     * </li></ul></p>
     *
     * @return sum of squared deviations of predicted y values
     */
    public double getRegressionSumSquares() {
        return getRegressionSumSquares(getSlope());
    }

    /**
     * Returns the sum of squared errors divided by the degrees of freedom,
     * usually abbreviated MSE.
     * <p>
     * If there are fewer than <strong>three</strong> data pairs in the model,
     * or if there is no variation in <code>x</code>, this returns
     * <code>Double.NaN</code>.</p>
     *
     * @return sum of squared deviations of y values
     */
    public double getMeanSquareError() {
        if (n < 3) {
            return Double.NaN;
        }
        return hasIntercept ? (getSumSquaredErrors() / (n - 2)) : (getSumSquaredErrors() / (n - 1));
    }

    /**
     * Returns <a href="http://mathworld.wolfram.com/CorrelationCoefficient.html">
     * Pearson's product moment correlation coefficient</a>,
     * usually denoted r.
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>At least two observations (with at least two different x values)
     * must have been added before invoking this method. If this method is
     * invoked before a model can be estimated, <code>Double,NaN</code> is
     * returned.
     * </li></ul></p>
     *
     * @return Pearson's r
     */
    public double getR() {
        double b1 = getSlope();
        double result = FastMath.sqrt(getRSquare());
        if (b1 < 0) {
            result = -result;
        }
        return result;
    }

    /**
     * Returns the <a href="http://www.xycoon.com/coefficient1.htm">
     * coefficient of determination</a>,
     * usually denoted r-square.
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>At least two observations (with at least two different x values)
     * must have been added before invoking this method. If this method is
     * invoked before a model can be estimated, <code>Double,NaN</code> is
     * returned.
     * </li></ul></p>
     *
     * @return r-square
     */
    public double getRSquare() {
        double ssto = getTotalSumSquares();
        return (ssto - getSumSquaredErrors()) / ssto;
    }

    /**
     * Returns the <a href="http://www.xycoon.com/standarderrorb0.htm">
     * standard error of the intercept estimate</a>,
     * usually denoted s(b0).
     * <p>
     * If there are fewer that <strong>three</strong> observations in the
     * model, or if there is no variation in x, this returns
     * <code>Double.NaN</code>.</p> Additionally, a <code>Double.NaN</code> is
     * returned when the intercept is constrained to be zero
     *
     * @return standard error associated with intercept estimate
     */
    public double getInterceptStdErr() {
        if( !hasIntercept ){
            return Double.NaN;
        }
        return FastMath.sqrt(
            getMeanSquareError() * ((1d / n) + (xbar * xbar) / sumXX));
    }

    /**
     * Returns the <a href="http://www.xycoon.com/standerrorb(1).htm">standard
     * error of the slope estimate</a>,
     * usually denoted s(b1).
     * <p>
     * If there are fewer that <strong>three</strong> data pairs in the model,
     * or if there is no variation in x, this returns <code>Double.NaN</code>.
     * </p>
     *
     * @return standard error associated with slope estimate
     */
    public double getSlopeStdErr() {
        return FastMath.sqrt(getMeanSquareError() / sumXX);
    }

    /**
     * Returns the half-width of a 95% confidence interval for the slope
     * estimate.
     * <p>
     * The 95% confidence interval is</p>
     * <p>
     * <code>(getSlope() - getSlopeConfidenceInterval(),
     * getSlope() + getSlopeConfidenceInterval())</code></p>
     * <p>
     * If there are fewer that <strong>three</strong> observations in the
     * model, or if there is no variation in x, this returns
     * <code>Double.NaN</code>.</p>
     * <p>
     * <strong>Usage Note</strong>:<br>
     * The validity of this statistic depends on the assumption that the
     * observations included in the model are drawn from a
     * <a href="http://mathworld.wolfram.com/BivariateNormalDistribution.html">
     * Bivariate Normal Distribution</a>.</p>
     *
     * @return half-width of 95% confidence interval for the slope estimate
     * @throws OutOfRangeException if the confidence interval can not be computed.
     */
    public double getSlopeConfidenceInterval() throws OutOfRangeException {
        return getSlopeConfidenceInterval(0.05d);
    }

    /**
     * Returns the half-width of a (100-100*alpha)% confidence interval for
     * the slope estimate.
     * <p>
     * The (100-100*alpha)% confidence interval is </p>
     * <p>
     * <code>(getSlope() - getSlopeConfidenceInterval(),
     * getSlope() + getSlopeConfidenceInterval())</code></p>
     * <p>
     * To request, for example, a 99% confidence interval, use
     * <code>alpha = .01</code></p>
     * <p>
     * <strong>Usage Note</strong>:<br>
     * The validity of this statistic depends on the assumption that the
     * observations included in the model are drawn from a
     * <a href="http://mathworld.wolfram.com/BivariateNormalDistribution.html">
     * Bivariate Normal Distribution</a>.</p>
     * <p>
     * <strong> Preconditions:</strong><ul>
     * <li>If there are fewer that <strong>three</strong> observations in the
     * model, or if there is no variation in x, this returns
     * <code>Double.NaN</code>.
     * </li>
     * <li><code>(0 < alpha < 1)</code>; otherwise an
     * <code>OutOfRangeException</code> is thrown.
     * </li></ul></p>
     *
     * @param alpha the desired significance level
     * @return half-width of 95% confidence interval for the slope estimate
     * @throws OutOfRangeException if the confidence interval can not be computed.
     */
    public double getSlopeConfidenceInterval(final double alpha)
    throws OutOfRangeException {
        if (n < 3) {
            return Double.NaN;
        }
        if (alpha >= 1 || alpha <= 0) {
            throw new OutOfRangeException(LocalizedFormats.SIGNIFICANCE_LEVEL,
                                          alpha, 0, 1);
        }
        // No advertised NotStrictlyPositiveException here - will return NaN above
        TDistribution distribution = new TDistribution(n - 2);
        return getSlopeStdErr() *
            distribution.inverseCumulativeProbability(1d - alpha / 2d);
    }

    /**
     * Returns the significance level of the slope (equiv) correlation.
     * <p>
     * Specifically, the returned value is the smallest <code>alpha</code>
     * such that the slope confidence interval with significance level
     * equal to <code>alpha</code> does not include <code>0</code>.
     * On regression output, this is often denoted <code>Prob(|t| > 0)</code>
     * </p><p>
     * <strong>Usage Note</strong>:<br>
     * The validity of this statistic depends on the assumption that the
     * observations included in the model are drawn from a
     * <a href="http://mathworld.wolfram.com/BivariateNormalDistribution.html">
     * Bivariate Normal Distribution</a>.</p>
     * <p>
     * If there are fewer that <strong>three</strong> observations in the
     * model, or if there is no variation in x, this returns
     * <code>Double.NaN</code>.</p>
     *
     * @return significance level for slope/correlation
     * @throws org.apache.commons.math3.exception.MaxCountExceededException
     * if the significance level can not be computed.
     */
    public double getSignificance() {
        if (n < 3) {
            return Double.NaN;
        }
        // No advertised NotStrictlyPositiveException here - will return NaN above
        TDistribution distribution = new TDistribution(n - 2);
        return 2d * (1.0 - distribution.cumulativeProbability(
                    FastMath.abs(getSlope()) / getSlopeStdErr()));
    }

    // ---------------------Private methods-----------------------------------

    /**
    * Returns the intercept of the estimated regression line, given the slope.
    * <p>
    * Will return <code>NaN</code> if slope is <code>NaN</code>.</p>
    *
    * @param slope current slope
    * @return the intercept of the regression line
    */
    private double getIntercept(final double slope) {
      if( hasIntercept){
        return (sumY - slope * sumX) / n;
      }
      return 0.0;
    }

    /**
     * Computes SSR from b1.
     *
     * @param slope regression slope estimate
     * @return sum of squared deviations of predicted y values
     */
    private double getRegressionSumSquares(final double slope) {
        return slope * slope * sumXX;
    }

    /**
     * Performs a regression on data present in buffers and outputs a RegressionResults object.
     *
     * <p>If there are fewer than 3 observations in the model and {@code hasIntercept} is true
     * a {@code NoDataException} is thrown.  If there is no intercept term, the model must
     * contain at least 2 observations.</p>
     *
     * @return RegressionResults acts as a container of regression output
     * @throws ModelSpecificationException if the model is not correctly specified
     * @throws NoDataException if there is not sufficient data in the model to
     * estimate the regression parameters
     */
    public RegressionResults regress() throws ModelSpecificationException, NoDataException {
        if (hasIntercept) {
            if (n < 3) {
                throw new NoDataException(LocalizedFormats.NOT_ENOUGH_DATA_REGRESSION);
            }
            if (FastMath.abs(sumXX) > Precision.SAFE_MIN) {
                final double[] params = new double[] { getIntercept(), getSlope() };
                final double mse = getMeanSquareError();
                final double _syy = sumYY + sumY * sumY / n;
                final double[] vcv = new double[] { mse * (xbar * xbar / sumXX + 1.0 / n), -xbar * mse / sumXX, mse / sumXX };
                return new RegressionResults(params, new double[][] { vcv }, true, n, 2, sumY, _syy, getSumSquaredErrors(), true,
                        false);
            } else {
                final double[] params = new double[] { sumY / n, Double.NaN };
                // final double mse = getMeanSquareError();
                final double[] vcv = new double[] { ybar / (n - 1.0), Double.NaN, Double.NaN };
                return new RegressionResults(params, new double[][] { vcv }, true, n, 1, sumY, sumYY, getSumSquaredErrors(), true,
                        false);
            }
        } else {
            if (n < 2) {
                throw new NoDataException(LocalizedFormats.NOT_ENOUGH_DATA_REGRESSION);
            }
            if (!Double.isNaN(sumXX)) {
                final double[] vcv = new double[] { getMeanSquareError() / sumXX };
                final double[] params = new double[] { sumXY / sumXX };
                return new RegressionResults(params, new double[][] { vcv }, true, n, 1, sumY, sumYY, getSumSquaredErrors(), false,
                        false);
            } else {
                final double[] vcv = new double[] { Double.NaN };
                final double[] params = new double[] { Double.NaN };
                return new RegressionResults(params, new double[][] { vcv }, true, n, 1, Double.NaN, Double.NaN, Double.NaN, false,
                        false);
            }
        }
    }

    /**
     * Performs a regression on data present in buffers including only regressors
     * indexed in variablesToInclude and outputs a RegressionResults object
     * @param variablesToInclude an array of indices of regressors to include
     * @return RegressionResults acts as a container of regression output
     * @throws MathIllegalArgumentException if the variablesToInclude array is null or zero length
     * @throws OutOfRangeException if a requested variable is not present in model
     */
    public RegressionResults regress(int[] variablesToInclude) throws MathIllegalArgumentException{
        if( variablesToInclude == null || variablesToInclude.length == 0){
          throw new MathIllegalArgumentException(LocalizedFormats.ARRAY_ZERO_LENGTH_OR_NULL_NOT_ALLOWED);
        }
        if( variablesToInclude.length > 2 || (variablesToInclude.length > 1 && !hasIntercept) ){
            throw new ModelSpecificationException(
                    LocalizedFormats.ARRAY_SIZE_EXCEEDS_MAX_VARIABLES,
                    (variablesToInclude.length > 1 && !hasIntercept) ? 1 : 2);
        }

        if( hasIntercept ){
            if( variablesToInclude.length == 2 ){
                if( variablesToInclude[0] == 1 ){
                    throw new ModelSpecificationException(LocalizedFormats.NOT_INCREASING_SEQUENCE);
                }else if( variablesToInclude[0] != 0 ){
                    throw new OutOfRangeException( variablesToInclude[0], 0,1 );
                }
                if( variablesToInclude[1] != 1){
                     throw new OutOfRangeException( variablesToInclude[0], 0,1 );
                }
                return regress();
            }else{
                if( variablesToInclude[0] != 1 && variablesToInclude[0] != 0 ){
                     throw new OutOfRangeException( variablesToInclude[0],0,1 );
                }
                final double _mean = sumY * sumY / n;
                final double _syy = sumYY + _mean;
                if( variablesToInclude[0] == 0 ){
                    //just the mean
                    final double[] vcv = new double[]{ sumYY/(((n-1)*n)) };
                    final double[] params = new double[]{ ybar };
                    return new RegressionResults(
                      params, new double[][]{vcv}, true, n, 1,
                      sumY, _syy+_mean, sumYY,true,false);

                }else if( variablesToInclude[0] == 1){
                    //final double _syy = sumYY + sumY * sumY / ((double) n);
                    final double _sxx = sumXX + sumX * sumX / n;
                    final double _sxy = sumXY + sumX * sumY / n;
                    final double _sse = FastMath.max(0d, _syy - _sxy * _sxy / _sxx);
                    final double _mse = _sse/((n-1));
                    if( !Double.isNaN(_sxx) ){
                        final double[] vcv = new double[]{ _mse / _sxx };
                        final double[] params = new double[]{ _sxy/_sxx };
                        return new RegressionResults(
                                    params, new double[][]{vcv}, true, n, 1,
                                    sumY, _syy, _sse,false,false);
                    }else{
                        final double[] vcv = new double[]{Double.NaN };
                        final double[] params = new double[]{ Double.NaN };
                        return new RegressionResults(
                                    params, new double[][]{vcv}, true, n, 1,
                                    Double.NaN, Double.NaN, Double.NaN,false,false);
                    }
                }
            }
        }else{
            if( variablesToInclude[0] != 0 ){
                throw new OutOfRangeException(variablesToInclude[0],0,0);
            }
            return regress();
        }

        return null;
    }
}
