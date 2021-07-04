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
package org.apache.commons.math3.fitting.leastsquares;

import org.apache.commons.math3.analysis.MultivariateMatrixFunction;
import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem.Evaluation;
import org.apache.commons.math3.linear.ArrayRealVector;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RealVector;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.optim.PointVectorValuePair;

/**
 * A mutable builder for {@link LeastSquaresProblem}s.
 *
 * @see LeastSquaresFactory
 * @since 3.3
 */
public class LeastSquaresBuilder {

    /** max evaluations */
    private int maxEvaluations;
    /** max iterations */
    private int maxIterations;
    /** convergence checker */
    private ConvergenceChecker<Evaluation> checker;
    /** model function */
    private MultivariateJacobianFunction model;
    /** observed values */
    private RealVector target;
    /** initial guess */
    private RealVector start;
    /** weight matrix */
    private RealMatrix weight;
    /**
     * Lazy evaluation.
     *
     * @since 3.4
     */
    private boolean lazyEvaluation;
    /** Validator.
     *
     * @since 3.4
     */
    private ParameterValidator paramValidator;


    /**
     * Construct a {@link LeastSquaresProblem} from the data in this builder.
     *
     * @return a new {@link LeastSquaresProblem}.
     */
    public LeastSquaresProblem build() {
        return LeastSquaresFactory.create(model,
                                          target,
                                          start,
                                          weight,
                                          checker,
                                          maxEvaluations,
                                          maxIterations,
                                          lazyEvaluation,
                                          paramValidator);
    }

    /**
     * Configure the max evaluations.
     *
     * @param newMaxEvaluations the maximum number of evaluations permitted.
     * @return this
     */
    public LeastSquaresBuilder maxEvaluations(final int newMaxEvaluations) {
        this.maxEvaluations = newMaxEvaluations;
        return this;
    }

    /**
     * Configure the max iterations.
     *
     * @param newMaxIterations the maximum number of iterations permitted.
     * @return this
     */
    public LeastSquaresBuilder maxIterations(final int newMaxIterations) {
        this.maxIterations = newMaxIterations;
        return this;
    }

    /**
     * Configure the convergence checker.
     *
     * @param newChecker the convergence checker.
     * @return this
     */
    public LeastSquaresBuilder checker(final ConvergenceChecker<Evaluation> newChecker) {
        this.checker = newChecker;
        return this;
    }

    /**
     * Configure the convergence checker.
     * <p/>
     * This function is an overloaded version of {@link #checker(ConvergenceChecker)}.
     *
     * @param newChecker the convergence checker.
     * @return this
     */
    public LeastSquaresBuilder checkerPair(final ConvergenceChecker<PointVectorValuePair> newChecker) {
        return this.checker(LeastSquaresFactory.evaluationChecker(newChecker));
    }

    /**
     * Configure the model function.
     *
     * @param value the model function value
     * @param jacobian the Jacobian of {@code value}
     * @return this
     */
    public LeastSquaresBuilder model(final MultivariateVectorFunction value,
                                     final MultivariateMatrixFunction jacobian) {
        return model(LeastSquaresFactory.model(value, jacobian));
    }

    /**
     * Configure the model function.
     *
     * @param newModel the model function value and Jacobian
     * @return this
     */
    public LeastSquaresBuilder model(final MultivariateJacobianFunction newModel) {
        this.model = newModel;
        return this;
    }

    /**
     * Configure the observed data.
     *
     * @param newTarget the observed data.
     * @return this
     */
    public LeastSquaresBuilder target(final RealVector newTarget) {
        this.target = newTarget;
        return this;
    }

    /**
     * Configure the observed data.
     *
     * @param newTarget the observed data.
     * @return this
     */
    public LeastSquaresBuilder target(final double[] newTarget) {
        return target(new ArrayRealVector(newTarget, false));
    }

    /**
     * Configure the initial guess.
     *
     * @param newStart the initial guess.
     * @return this
     */
    public LeastSquaresBuilder start(final RealVector newStart) {
        this.start = newStart;
        return this;
    }

    /**
     * Configure the initial guess.
     *
     * @param newStart the initial guess.
     * @return this
     */
    public LeastSquaresBuilder start(final double[] newStart) {
        return start(new ArrayRealVector(newStart, false));
    }

    /**
     * Configure the weight matrix.
     *
     * @param newWeight the weight matrix
     * @return this
     */
    public LeastSquaresBuilder weight(final RealMatrix newWeight) {
        this.weight = newWeight;
        return this;
    }

    /**
     * Configure whether evaluation will be lazy or not.
     *
     * @param newValue Whether to perform lazy evaluation.
     * @return this object.
     *
     * @since 3.4
     */
    public LeastSquaresBuilder lazyEvaluation(final boolean newValue) {
        lazyEvaluation = newValue;
        return this;
    }

    /**
     * Configure the validator of the model parameters.
     *
     * @param newValidator Parameter validator.
     * @return this object.
     *
     * @since 3.4
     */
    public LeastSquaresBuilder parameterValidator(final ParameterValidator newValidator) {
        paramValidator = newValidator;
        return this;
    }
}
