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

import org.apache.commons.math3.util.IterationEvent;
import org.apache.commons.math3.exception.MathUnsupportedOperationException;

/**
 * This is the base class for all events occurring during the iterations of a
 * {@link IterativeLinearSolver}.
 *
 * @since 3.0
 */
public abstract class IterativeLinearSolverEvent
    extends IterationEvent {
    /** Serialization identifier. */
    private static final long serialVersionUID = 20120129L;

    /**
     * Creates a new instance of this class.
     *
     * @param source the iterative algorithm on which the event initially
     * occurred
     * @param iterations the number of iterations performed at the time
     * {@code this} event is created
     */
    public IterativeLinearSolverEvent(final Object source, final int iterations) {
        super(source, iterations);
    }

    /**
     * Returns the current right-hand side of the linear system to be solved.
     * This method should return an unmodifiable view, or a deep copy of the
     * actual right-hand side vector, in order not to compromise subsequent
     * iterations of the source {@link IterativeLinearSolver}.
     *
     * @return the right-hand side vector, b
     */
    public abstract RealVector getRightHandSideVector();

    /**
     * Returns the norm of the residual. The returned value is not required to
     * be <em>exact</em>. Instead, the norm of the so-called <em>updated</em>
     * residual (if available) should be returned. For example, the
     * {@link ConjugateGradient conjugate gradient} method computes a sequence
     * of residuals, the norm of which is cheap to compute. However, due to
     * accumulation of round-off errors, this residual might differ from the
     * true residual after some iterations. See e.g. A. Greenbaum and
     * Z. Strakos, <em>Predicting the Behavior of Finite Precision Lanzos and
     * Conjugate Gradient Computations</em>, Technical Report 538, Department of
     * Computer Science, New York University, 1991 (available
     * <a href="http://www.archive.org/details/predictingbehavi00gree">here</a>).
     *
     * @return the norm of the residual, ||r||
     */
    public abstract double getNormOfResidual();

    /**
     * <p>
     * Returns the residual. This is an optional operation, as all iterative
     * linear solvers do not provide cheap estimate of the updated residual
     * vector, in which case
     * </p>
     * <ul>
     * <li>this method should throw a
     * {@link MathUnsupportedOperationException},</li>
     * <li>{@link #providesResidual()} returns {@code false}.</li>
     * </ul>
     * <p>
     * The default implementation throws a
     * {@link MathUnsupportedOperationException}. If this method is overriden,
     * then {@link #providesResidual()} should be overriden as well.
     * </p>
     *
     * @return the updated residual, r
     */
    public RealVector getResidual() {
        throw new MathUnsupportedOperationException();
    }

    /**
     * Returns the current estimate of the solution to the linear system to be
     * solved. This method should return an unmodifiable view, or a deep copy of
     * the actual current solution, in order not to compromise subsequent
     * iterations of the source {@link IterativeLinearSolver}.
     *
     * @return the solution, x
     */
    public abstract RealVector getSolution();

    /**
     * Returns {@code true} if {@link #getResidual()} is supported. The default
     * implementation returns {@code false}.
     *
     * @return {@code false} if {@link #getResidual()} throws a
     * {@link MathUnsupportedOperationException}
     */
    public boolean providesResidual() {
        return false;
    }
}
