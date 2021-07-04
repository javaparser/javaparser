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

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.ExceptionContext;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.IterationManager;
import org.apache.commons.math3.util.MathUtils;

/**
 * <p>
 * Implementation of the SYMMLQ iterative linear solver proposed by <a
 * href="#PAIG1975">Paige and Saunders (1975)</a>. This implementation is
 * largely based on the FORTRAN code by Pr. Michael A. Saunders, available <a
 * href="http://www.stanford.edu/group/SOL/software/symmlq/f77/">here</a>.
 * </p>
 * <p>
 * SYMMLQ is designed to solve the system of linear equations A &middot; x = b
 * where A is an n &times; n self-adjoint linear operator (defined as a
 * {@link RealLinearOperator}), and b is a given vector. The operator A is not
 * required to be positive definite. If A is known to be definite, the method of
 * conjugate gradients might be preferred, since it will require about the same
 * number of iterations as SYMMLQ but slightly less work per iteration.
 * </p>
 * <p>
 * SYMMLQ is designed to solve the system (A - shift &middot; I) &middot; x = b,
 * where shift is a specified scalar value. If shift and b are suitably chosen,
 * the computed vector x may approximate an (unnormalized) eigenvector of A, as
 * in the methods of inverse iteration and/or Rayleigh-quotient iteration.
 * Again, the linear operator (A - shift &middot; I) need not be positive
 * definite (but <em>must</em> be self-adjoint). The work per iteration is very
 * slightly less if shift = 0.
 * </p>
 * <h3>Preconditioning</h3>
 * <p>
 * Preconditioning may reduce the number of iterations required. The solver may
 * be provided with a positive definite preconditioner
 * M = P<sup>T</sup> &middot; P
 * that is known to approximate
 * (A - shift &middot; I)<sup>-1</sup> in some sense, where matrix-vector
 * products of the form M &middot; y = x can be computed efficiently. Then
 * SYMMLQ will implicitly solve the system of equations
 * P &middot; (A - shift &middot; I) &middot; P<sup>T</sup> &middot;
 * x<sub>hat</sub> = P &middot; b, i.e.
 * A<sub>hat</sub> &middot; x<sub>hat</sub> = b<sub>hat</sub>,
 * where
 * A<sub>hat</sub> = P &middot; (A - shift &middot; I) &middot; P<sup>T</sup>,
 * b<sub>hat</sub> = P &middot; b,
 * and return the solution
 * x = P<sup>T</sup> &middot; x<sub>hat</sub>.
 * The associated residual is
 * r<sub>hat</sub> = b<sub>hat</sub> - A<sub>hat</sub> &middot; x<sub>hat</sub>
 *                 = P &middot; [b - (A - shift &middot; I) &middot; x]
 *                 = P &middot; r.
 * </p>
 * <p>
 * In the case of preconditioning, the {@link IterativeLinearSolverEvent}s that
 * this solver fires are such that
 * {@link IterativeLinearSolverEvent#getNormOfResidual()} returns the norm of
 * the <em>preconditioned</em>, updated residual, ||P &middot; r||, not the norm
 * of the <em>true</em> residual ||r||.
 * </p>
 * <h3><a id="stopcrit">Default stopping criterion</a></h3>
 * <p>
 * A default stopping criterion is implemented. The iterations stop when || rhat
 * || &le; &delta; || Ahat || || xhat ||, where xhat is the current estimate of
 * the solution of the transformed system, rhat the current estimate of the
 * corresponding residual, and &delta; a user-specified tolerance.
 * </p>
 * <h3>Iteration count</h3>
 * <p>
 * In the present context, an iteration should be understood as one evaluation
 * of the matrix-vector product A &middot; x. The initialization phase therefore
 * counts as one iteration. If the user requires checks on the symmetry of A,
 * this entails one further matrix-vector product in the initial phase. This
 * further product is <em>not</em> accounted for in the iteration count. In
 * other words, the number of iterations required to reach convergence will be
 * identical, whether checks have been required or not.
 * </p>
 * <p>
 * The present definition of the iteration count differs from that adopted in
 * the original FOTRAN code, where the initialization phase was <em>not</em>
 * taken into account.
 * </p>
 * <h3><a id="initguess">Initial guess of the solution</a></h3>
 * <p>
 * The {@code x} parameter in
 * <ul>
 * <li>{@link #solve(RealLinearOperator, RealVector, RealVector)},</li>
 * <li>{@link #solve(RealLinearOperator, RealLinearOperator, RealVector, RealVector)}},</li>
 * <li>{@link #solveInPlace(RealLinearOperator, RealVector, RealVector)},</li>
 * <li>{@link #solveInPlace(RealLinearOperator, RealLinearOperator, RealVector, RealVector)},</li>
 * <li>{@link #solveInPlace(RealLinearOperator, RealLinearOperator, RealVector, RealVector, boolean, double)},</li>
 * </ul>
 * should not be considered as an initial guess, as it is set to zero in the
 * initial phase. If x<sub>0</sub> is known to be a good approximation to x, one
 * should compute r<sub>0</sub> = b - A &middot; x, solve A &middot; dx = r0,
 * and set x = x<sub>0</sub> + dx.
 * </p>
 * <h3><a id="context">Exception context</a></h3>
 * <p>
 * Besides standard {@link DimensionMismatchException}, this class might throw
 * {@link NonSelfAdjointOperatorException} if the linear operator or the
 * preconditioner are not symmetric. In this case, the {@link ExceptionContext}
 * provides more information
 * <ul>
 * <li>key {@code "operator"} points to the offending linear operator, say L,</li>
 * <li>key {@code "vector1"} points to the first offending vector, say x,
 * <li>key {@code "vector2"} points to the second offending vector, say y, such
 * that x<sup>T</sup> &middot; L &middot; y &ne; y<sup>T</sup> &middot; L
 * &middot; x (within a certain accuracy).</li>
 * </ul>
 * </p>
 * <p>
 * {@link NonPositiveDefiniteOperatorException} might also be thrown in case the
 * preconditioner is not positive definite. The relevant keys to the
 * {@link ExceptionContext} are
 * <ul>
 * <li>key {@code "operator"}, which points to the offending linear operator,
 * say L,</li>
 * <li>key {@code "vector"}, which points to the offending vector, say x, such
 * that x<sup>T</sup> &middot; L &middot; x < 0.</li>
 * </ul>
 * </p>
 * <h3>References</h3>
 * <dl>
 * <dt><a id="PAIG1975">Paige and Saunders (1975)</a></dt>
 * <dd>C. C. Paige and M. A. Saunders, <a
 * href="http://www.stanford.edu/group/SOL/software/symmlq/PS75.pdf"><em>
 * Solution of Sparse Indefinite Systems of Linear Equations</em></a>, SIAM
 * Journal on Numerical Analysis 12(4): 617-629, 1975</dd>
 * </dl>
 *
 * @since 3.0
 */
public class SymmLQ
    extends PreconditionedIterativeLinearSolver {

    /*
     * IMPLEMENTATION NOTES
     * --------------------
     * The implementation follows as closely as possible the notations of Paige
     * and Saunders (1975). Attention must be paid to the fact that some
     * quantities which are relevant to iteration k can only be computed in
     * iteration (k+1). Therefore, minute attention must be paid to the index of
     * each state variable of this algorithm.
     *
     * 1. Preconditioning
     *    ---------------
     * The Lanczos iterations associated with Ahat and bhat read
     *   beta[1] = ||P * b||
     *   v[1] = P * b / beta[1]
     *   beta[k+1] * v[k+1] = Ahat * v[k] - alpha[k] * v[k] - beta[k] * v[k-1]
     *                      = P * (A - shift * I) * P' * v[k] - alpha[k] * v[k]
     *                        - beta[k] * v[k-1]
     * Multiplying both sides by P', we get
     *   beta[k+1] * (P' * v)[k+1] = M * (A - shift * I) * (P' * v)[k]
     *                               - alpha[k] * (P' * v)[k]
     *                               - beta[k] * (P' * v[k-1]),
     * and
     *   alpha[k+1] = v[k+1]' * Ahat * v[k+1]
     *              = v[k+1]' * P * (A - shift * I) * P' * v[k+1]
     *              = (P' * v)[k+1]' * (A - shift * I) * (P' * v)[k+1].
     *
     * In other words, the Lanczos iterations are unchanged, except for the fact
     * that we really compute (P' * v) instead of v. It can easily be checked
     * that all other formulas are unchanged. It must be noted that P is never
     * explicitly used, only matrix-vector products involving are invoked.
     *
     * 2. Accounting for the shift parameter
     *    ----------------------------------
     * Is trivial: each time A.operate(x) is invoked, one must subtract shift * x
     * to the result.
     *
     * 3. Accounting for the goodb flag
     *    -----------------------------
     * When goodb is set to true, the component of xL along b is computed
     * separately. From Paige and Saunders (1975), equation (5.9), we have
     *   wbar[k+1] = s[k] * wbar[k] - c[k] * v[k+1],
     *   wbar[1] = v[1].
     * Introducing wbar2[k] = wbar[k] - s[1] * ... * s[k-1] * v[1], it can
     * easily be verified by induction that wbar2 follows the same recursive
     * relation
     *   wbar2[k+1] = s[k] * wbar2[k] - c[k] * v[k+1],
     *   wbar2[1] = 0,
     * and we then have
     *   w[k] = c[k] * wbar2[k] + s[k] * v[k+1]
     *          + s[1] * ... * s[k-1] * c[k] * v[1].
     * Introducing w2[k] = w[k] - s[1] * ... * s[k-1] * c[k] * v[1], we find,
     * from (5.10)
     *   xL[k] = zeta[1] * w[1] + ... + zeta[k] * w[k]
     *         = zeta[1] * w2[1] + ... + zeta[k] * w2[k]
     *           + (s[1] * c[2] * zeta[2] + ...
     *           + s[1] * ... * s[k-1] * c[k] * zeta[k]) * v[1]
     *         = xL2[k] + bstep[k] * v[1],
     * where xL2[k] is defined by
     *   xL2[0] = 0,
     *   xL2[k+1] = xL2[k] + zeta[k+1] * w2[k+1],
     * and bstep is defined by
     *   bstep[1] = 0,
     *   bstep[k] = bstep[k-1] + s[1] * ... * s[k-1] * c[k] * zeta[k].
     * We also have, from (5.11)
     *   xC[k] = xL[k-1] + zbar[k] * wbar[k]
     *         = xL2[k-1] + zbar[k] * wbar2[k]
     *           + (bstep[k-1] + s[1] * ... * s[k-1] * zbar[k]) * v[1].
     */

    /**
     * <p>
     * A simple container holding the non-final variables used in the
     * iterations. Making the current state of the solver visible from the
     * outside is necessary, because during the iterations, {@code x} does not
     * <em>exactly</em> hold the current estimate of the solution. Indeed,
     * {@code x} needs in general to be moved from the LQ point to the CG point.
     * Besides, additional upudates must be carried out in case {@code goodb} is
     * set to {@code true}.
     * </p>
     * <p>
     * In all subsequent comments, the description of the state variables refer
     * to their value after a call to {@link #update()}. In these comments, k is
     * the current number of evaluations of matrix-vector products.
     * </p>
     */
    private static class State {
        /** The cubic root of {@link #MACH_PREC}. */
        static final double CBRT_MACH_PREC;

        /** The machine precision. */
        static final double MACH_PREC;

        /** Reference to the linear operator. */
        private final RealLinearOperator a;

        /** Reference to the right-hand side vector. */
        private final RealVector b;

        /** {@code true} if symmetry of matrix and conditioner must be checked. */
        private final boolean check;

        /**
         * The value of the custom tolerance &delta; for the default stopping
         * criterion.
         */
        private final double delta;

        /** The value of beta[k+1]. */
        private double beta;

        /** The value of beta[1]. */
        private double beta1;

        /** The value of bstep[k-1]. */
        private double bstep;

        /** The estimate of the norm of P * rC[k]. */
        private double cgnorm;

        /** The value of dbar[k+1] = -beta[k+1] * c[k-1]. */
        private double dbar;

        /**
         * The value of gamma[k] * zeta[k]. Was called {@code rhs1} in the
         * initial code.
         */
        private double gammaZeta;

        /** The value of gbar[k]. */
        private double gbar;

        /** The value of max(|alpha[1]|, gamma[1], ..., gamma[k-1]). */
        private double gmax;

        /** The value of min(|alpha[1]|, gamma[1], ..., gamma[k-1]). */
        private double gmin;

        /** Copy of the {@code goodb} parameter. */
        private final boolean goodb;

        /** {@code true} if the default convergence criterion is verified. */
        private boolean hasConverged;

        /** The estimate of the norm of P * rL[k-1]. */
        private double lqnorm;

        /** Reference to the preconditioner, M. */
        private final RealLinearOperator m;

        /**
         * The value of (-eps[k+1] * zeta[k-1]). Was called {@code rhs2} in the
         * initial code.
         */
        private double minusEpsZeta;

        /** The value of M * b. */
        private final RealVector mb;

        /** The value of beta[k]. */
        private double oldb;

        /** The value of beta[k] * M^(-1) * P' * v[k]. */
        private RealVector r1;

        /** The value of beta[k+1] * M^(-1) * P' * v[k+1]. */
        private RealVector r2;

        /**
         * The value of the updated, preconditioned residual P * r. This value is
         * given by {@code min(}{@link #cgnorm}{@code , }{@link #lqnorm}{@code )}.
         */
        private double rnorm;

        /** Copy of the {@code shift} parameter. */
        private final double shift;

        /** The value of s[1] * ... * s[k-1]. */
        private double snprod;

        /**
         * An estimate of the square of the norm of A * V[k], based on Paige and
         * Saunders (1975), equation (3.3).
         */
        private double tnorm;

        /**
         * The value of P' * wbar[k] or P' * (wbar[k] - s[1] * ... * s[k-1] *
         * v[1]) if {@code goodb} is {@code true}. Was called {@code w} in the
         * initial code.
         */
        private RealVector wbar;

        /**
         * A reference to the vector to be updated with the solution. Contains
         * the value of xL[k-1] if {@code goodb} is {@code false}, (xL[k-1] -
         * bstep[k-1] * v[1]) otherwise.
         */
        private final RealVector xL;

        /** The value of beta[k+1] * P' * v[k+1]. */
        private RealVector y;

        /** The value of zeta[1]^2 + ... + zeta[k-1]^2. */
        private double ynorm2;

        /** The value of {@code b == 0} (exact floating-point equality). */
        private boolean bIsNull;

        static {
            MACH_PREC = FastMath.ulp(1.);
            CBRT_MACH_PREC = FastMath.cbrt(MACH_PREC);
        }

        /**
         * Creates and inits to k = 1 a new instance of this class.
         *
         * @param a the linear operator A of the system
         * @param m the preconditioner, M (can be {@code null})
         * @param b the right-hand side vector
         * @param goodb usually {@code false}, except if {@code x} is expected
         * to contain a large multiple of {@code b}
         * @param shift the amount to be subtracted to all diagonal elements of
         * A
         * @param delta the &delta; parameter for the default stopping criterion
         * @param check {@code true} if self-adjointedness of both matrix and
         * preconditioner should be checked
         */
        State(final RealLinearOperator a,
            final RealLinearOperator m,
            final RealVector b,
            final boolean goodb,
            final double shift,
            final double delta,
            final boolean check) {
            this.a = a;
            this.m = m;
            this.b = b;
            this.xL = new ArrayRealVector(b.getDimension());
            this.goodb = goodb;
            this.shift = shift;
            this.mb = m == null ? b : m.operate(b);
            this.hasConverged = false;
            this.check = check;
            this.delta = delta;
        }

        /**
         * Performs a symmetry check on the specified linear operator, and throws an
         * exception in case this check fails. Given a linear operator L, and a
         * vector x, this method checks that
         * x' &middot; L &middot; y = y' &middot; L &middot; x
         * (within a given accuracy), where y = L &middot; x.
         *
         * @param l the linear operator L
         * @param x the candidate vector x
         * @param y the candidate vector y = L &middot; x
         * @param z the vector z = L &middot; y
         * @throws NonSelfAdjointOperatorException when the test fails
         */
        private static void checkSymmetry(final RealLinearOperator l,
            final RealVector x, final RealVector y, final RealVector z)
            throws NonSelfAdjointOperatorException {
            final double s = y.dotProduct(y);
            final double t = x.dotProduct(z);
            final double epsa = (s + MACH_PREC) * CBRT_MACH_PREC;
            if (FastMath.abs(s - t) > epsa) {
                final NonSelfAdjointOperatorException e;
                e = new NonSelfAdjointOperatorException();
                final ExceptionContext context = e.getContext();
                context.setValue(SymmLQ.OPERATOR, l);
                context.setValue(SymmLQ.VECTOR1, x);
                context.setValue(SymmLQ.VECTOR2, y);
                context.setValue(SymmLQ.THRESHOLD, Double.valueOf(epsa));
                throw e;
            }
        }

        /**
         * Throws a new {@link NonPositiveDefiniteOperatorException} with
         * appropriate context.
         *
         * @param l the offending linear operator
         * @param v the offending vector
         * @throws NonPositiveDefiniteOperatorException in any circumstances
         */
        private static void throwNPDLOException(final RealLinearOperator l,
            final RealVector v) throws NonPositiveDefiniteOperatorException {
            final NonPositiveDefiniteOperatorException e;
            e = new NonPositiveDefiniteOperatorException();
            final ExceptionContext context = e.getContext();
            context.setValue(OPERATOR, l);
            context.setValue(VECTOR, v);
            throw e;
        }

        /**
         * A clone of the BLAS {@code DAXPY} function, which carries out the
         * operation y &larr; a &middot; x + y. This is for internal use only: no
         * dimension checks are provided.
         *
         * @param a the scalar by which {@code x} is to be multiplied
         * @param x the vector to be added to {@code y}
         * @param y the vector to be incremented
         */
        private static void daxpy(final double a, final RealVector x,
            final RealVector y) {
            final int n = x.getDimension();
            for (int i = 0; i < n; i++) {
                y.setEntry(i, a * x.getEntry(i) + y.getEntry(i));
            }
        }

        /**
         * A BLAS-like function, for the operation z &larr; a &middot; x + b
         * &middot; y + z. This is for internal use only: no dimension checks are
         * provided.
         *
         * @param a the scalar by which {@code x} is to be multiplied
         * @param x the first vector to be added to {@code z}
         * @param b the scalar by which {@code y} is to be multiplied
         * @param y the second vector to be added to {@code z}
         * @param z the vector to be incremented
         */
        private static void daxpbypz(final double a, final RealVector x,
            final double b, final RealVector y, final RealVector z) {
            final int n = z.getDimension();
            for (int i = 0; i < n; i++) {
                final double zi;
                zi = a * x.getEntry(i) + b * y.getEntry(i) + z.getEntry(i);
                z.setEntry(i, zi);
            }
        }

        /**
         * <p>
         * Move to the CG point if it seems better. In this version of SYMMLQ,
         * the convergence tests involve only cgnorm, so we're unlikely to stop
         * at an LQ point, except if the iteration limit interferes.
         * </p>
         * <p>
         * Additional upudates are also carried out in case {@code goodb} is set
         * to {@code true}.
         * </p>
         *
         * @param x the vector to be updated with the refined value of xL
         */
         void refineSolution(final RealVector x) {
            final int n = this.xL.getDimension();
            if (lqnorm < cgnorm) {
                if (!goodb) {
                    x.setSubVector(0, this.xL);
                } else {
                    final double step = bstep / beta1;
                    for (int i = 0; i < n; i++) {
                        final double bi = mb.getEntry(i);
                        final double xi = this.xL.getEntry(i);
                        x.setEntry(i, xi + step * bi);
                    }
                }
            } else {
                final double anorm = FastMath.sqrt(tnorm);
                final double diag = gbar == 0. ? anorm * MACH_PREC : gbar;
                final double zbar = gammaZeta / diag;
                final double step = (bstep + snprod * zbar) / beta1;
                // ynorm = FastMath.sqrt(ynorm2 + zbar * zbar);
                if (!goodb) {
                    for (int i = 0; i < n; i++) {
                        final double xi = this.xL.getEntry(i);
                        final double wi = wbar.getEntry(i);
                        x.setEntry(i, xi + zbar * wi);
                    }
                } else {
                    for (int i = 0; i < n; i++) {
                        final double xi = this.xL.getEntry(i);
                        final double wi = wbar.getEntry(i);
                        final double bi = mb.getEntry(i);
                        x.setEntry(i, xi + zbar * wi + step * bi);
                    }
                }
            }
        }

        /**
         * Performs the initial phase of the SYMMLQ algorithm. On return, the
         * value of the state variables of {@code this} object correspond to k =
         * 1.
         */
         void init() {
            this.xL.set(0.);
            /*
             * Set up y for the first Lanczos vector. y and beta1 will be zero
             * if b = 0.
             */
            this.r1 = this.b.copy();
            this.y = this.m == null ? this.b.copy() : this.m.operate(this.r1);
            if ((this.m != null) && this.check) {
                checkSymmetry(this.m, this.r1, this.y, this.m.operate(this.y));
            }

            this.beta1 = this.r1.dotProduct(this.y);
            if (this.beta1 < 0.) {
                throwNPDLOException(this.m, this.y);
            }
            if (this.beta1 == 0.) {
                /* If b = 0 exactly, stop with x = 0. */
                this.bIsNull = true;
                return;
            }
            this.bIsNull = false;
            this.beta1 = FastMath.sqrt(this.beta1);
            /* At this point
             *   r1 = b,
             *   y = M * b,
             *   beta1 = beta[1].
             */
            final RealVector v = this.y.mapMultiply(1. / this.beta1);
            this.y = this.a.operate(v);
            if (this.check) {
                checkSymmetry(this.a, v, this.y, this.a.operate(this.y));
            }
            /*
             * Set up y for the second Lanczos vector. y and beta will be zero
             * or very small if b is an eigenvector.
             */
            daxpy(-this.shift, v, this.y);
            final double alpha = v.dotProduct(this.y);
            daxpy(-alpha / this.beta1, this.r1, this.y);
            /*
             * At this point
             *   alpha = alpha[1]
             *   y     = beta[2] * M^(-1) * P' * v[2]
             */
            /* Make sure r2 will be orthogonal to the first v. */
            final double vty = v.dotProduct(this.y);
            final double vtv = v.dotProduct(v);
            daxpy(-vty / vtv, v, this.y);
            this.r2 = this.y.copy();
            if (this.m != null) {
                this.y = this.m.operate(this.r2);
            }
            this.oldb = this.beta1;
            this.beta = this.r2.dotProduct(this.y);
            if (this.beta < 0.) {
                throwNPDLOException(this.m, this.y);
            }
            this.beta = FastMath.sqrt(this.beta);
            /*
             * At this point
             *   oldb = beta[1]
             *   beta = beta[2]
             *   y  = beta[2] * P' * v[2]
             *   r2 = beta[2] * M^(-1) * P' * v[2]
             */
            this.cgnorm = this.beta1;
            this.gbar = alpha;
            this.dbar = this.beta;
            this.gammaZeta = this.beta1;
            this.minusEpsZeta = 0.;
            this.bstep = 0.;
            this.snprod = 1.;
            this.tnorm = alpha * alpha + this.beta * this.beta;
            this.ynorm2 = 0.;
            this.gmax = FastMath.abs(alpha) + MACH_PREC;
            this.gmin = this.gmax;

            if (this.goodb) {
                this.wbar = new ArrayRealVector(this.a.getRowDimension());
                this.wbar.set(0.);
            } else {
                this.wbar = v;
            }
            updateNorms();
        }

        /**
         * Performs the next iteration of the algorithm. The iteration count
         * should be incremented prior to calling this method. On return, the
         * value of the state variables of {@code this} object correspond to the
         * current iteration count {@code k}.
         */
        void update() {
            final RealVector v = y.mapMultiply(1. / beta);
            y = a.operate(v);
            daxpbypz(-shift, v, -beta / oldb, r1, y);
            final double alpha = v.dotProduct(y);
            /*
             * At this point
             *   v     = P' * v[k],
             *   y     = (A - shift * I) * P' * v[k] - beta[k] * M^(-1) * P' * v[k-1],
             *   alpha = v'[k] * P * (A - shift * I) * P' * v[k]
             *           - beta[k] * v[k]' * P * M^(-1) * P' * v[k-1]
             *         = v'[k] * P * (A - shift * I) * P' * v[k]
             *           - beta[k] * v[k]' * v[k-1]
             *         = alpha[k].
             */
            daxpy(-alpha / beta, r2, y);
            /*
             * At this point
             *   y = (A - shift * I) * P' * v[k] - alpha[k] * M^(-1) * P' * v[k]
             *       - beta[k] * M^(-1) * P' * v[k-1]
             *     = M^(-1) * P' * (P * (A - shift * I) * P' * v[k] -alpha[k] * v[k]
             *       - beta[k] * v[k-1])
             *     = beta[k+1] * M^(-1) * P' * v[k+1],
             * from Paige and Saunders (1975), equation (3.2).
             *
             * WATCH-IT: the two following lines work only because y is no longer
             * updated up to the end of the present iteration, and is
             * reinitialized at the beginning of the next iteration.
             */
            r1 = r2;
            r2 = y;
            if (m != null) {
                y = m.operate(r2);
            }
            oldb = beta;
            beta = r2.dotProduct(y);
            if (beta < 0.) {
                throwNPDLOException(m, y);
            }
            beta = FastMath.sqrt(beta);
            /*
             * At this point
             *   r1 = beta[k] * M^(-1) * P' * v[k],
             *   r2 = beta[k+1] * M^(-1) * P' * v[k+1],
             *   y  = beta[k+1] * P' * v[k+1],
             *   oldb = beta[k],
             *   beta = beta[k+1].
             */
            tnorm += alpha * alpha + oldb * oldb + beta * beta;
            /*
             * Compute the next plane rotation for Q. See Paige and Saunders
             * (1975), equation (5.6), with
             *   gamma = gamma[k-1],
             *   c     = c[k-1],
             *   s     = s[k-1].
             */
            final double gamma = FastMath.sqrt(gbar * gbar + oldb * oldb);
            final double c = gbar / gamma;
            final double s = oldb / gamma;
            /*
             * The relations
             *   gbar[k] = s[k-1] * (-c[k-2] * beta[k]) - c[k-1] * alpha[k]
             *           = s[k-1] * dbar[k] - c[k-1] * alpha[k],
             *   delta[k] = c[k-1] * dbar[k] + s[k-1] * alpha[k],
             * are not stated in Paige and Saunders (1975), but can be retrieved
             * by expanding the (k, k-1) and (k, k) coefficients of the matrix in
             * equation (5.5).
             */
            final double deltak = c * dbar + s * alpha;
            gbar = s * dbar - c * alpha;
            final double eps = s * beta;
            dbar = -c * beta;
            final double zeta = gammaZeta / gamma;
            /*
             * At this point
             *   gbar   = gbar[k]
             *   deltak = delta[k]
             *   eps    = eps[k+1]
             *   dbar   = dbar[k+1]
             *   zeta   = zeta[k-1]
             */
            final double zetaC = zeta * c;
            final double zetaS = zeta * s;
            final int n = xL.getDimension();
            for (int i = 0; i < n; i++) {
                final double xi = xL.getEntry(i);
                final double vi = v.getEntry(i);
                final double wi = wbar.getEntry(i);
                xL.setEntry(i, xi + wi * zetaC + vi * zetaS);
                wbar.setEntry(i, wi * s - vi * c);
            }
            /*
             * At this point
             *   x = xL[k-1],
             *   ptwbar = P' wbar[k],
             * see Paige and Saunders (1975), equations (5.9) and (5.10).
             */
            bstep += snprod * c * zeta;
            snprod *= s;
            gmax = FastMath.max(gmax, gamma);
            gmin = FastMath.min(gmin, gamma);
            ynorm2 += zeta * zeta;
            gammaZeta = minusEpsZeta - deltak * zeta;
            minusEpsZeta = -eps * zeta;
            /*
             * At this point
             *   snprod       = s[1] * ... * s[k-1],
             *   gmax         = max(|alpha[1]|, gamma[1], ..., gamma[k-1]),
             *   gmin         = min(|alpha[1]|, gamma[1], ..., gamma[k-1]),
             *   ynorm2       = zeta[1]^2 + ... + zeta[k-1]^2,
             *   gammaZeta    = gamma[k] * zeta[k],
             *   minusEpsZeta = -eps[k+1] * zeta[k-1].
             * The relation for gammaZeta can be retrieved from Paige and
             * Saunders (1975), equation (5.4a), last line of the vector
             * gbar[k] * zbar[k] = -eps[k] * zeta[k-2] - delta[k] * zeta[k-1].
             */
            updateNorms();
        }

        /**
         * Computes the norms of the residuals, and checks for convergence.
         * Updates {@link #lqnorm} and {@link #cgnorm}.
         */
        private void updateNorms() {
            final double anorm = FastMath.sqrt(tnorm);
            final double ynorm = FastMath.sqrt(ynorm2);
            final double epsa = anorm * MACH_PREC;
            final double epsx = anorm * ynorm * MACH_PREC;
            final double epsr = anorm * ynorm * delta;
            final double diag = gbar == 0. ? epsa : gbar;
            lqnorm = FastMath.sqrt(gammaZeta * gammaZeta +
                                   minusEpsZeta * minusEpsZeta);
            final double qrnorm = snprod * beta1;
            cgnorm = qrnorm * beta / FastMath.abs(diag);

            /*
             * Estimate cond(A). In this version we look at the diagonals of L
             * in the factorization of the tridiagonal matrix, T = L * Q.
             * Sometimes, T[k] can be misleadingly ill-conditioned when T[k+1]
             * is not, so we must be careful not to overestimate acond.
             */
            final double acond;
            if (lqnorm <= cgnorm) {
                acond = gmax / gmin;
            } else {
                acond = gmax / FastMath.min(gmin, FastMath.abs(diag));
            }
            if (acond * MACH_PREC >= 0.1) {
                throw new IllConditionedOperatorException(acond);
            }
            if (beta1 <= epsx) {
                /*
                 * x has converged to an eigenvector of A corresponding to the
                 * eigenvalue shift.
                 */
                throw new SingularOperatorException();
            }
            rnorm = FastMath.min(cgnorm, lqnorm);
            hasConverged = (cgnorm <= epsx) || (cgnorm <= epsr);
        }

        /**
         * Returns {@code true} if the default stopping criterion is fulfilled.
         *
         * @return {@code true} if convergence of the iterations has occurred
         */
        boolean hasConverged() {
            return hasConverged;
        }

        /**
         * Returns {@code true} if the right-hand side vector is zero exactly.
         *
         * @return the boolean value of {@code b == 0}
         */
        boolean bEqualsNullVector() {
            return bIsNull;
        }

        /**
         * Returns {@code true} if {@code beta} is essentially zero. This method
         * is used to check for early stop of the iterations.
         *
         * @return {@code true} if {@code beta < }{@link #MACH_PREC}
         */
        boolean betaEqualsZero() {
            return beta < MACH_PREC;
        }

        /**
         * Returns the norm of the updated, preconditioned residual.
         *
         * @return the norm of the residual, ||P * r||
         */
        double getNormOfResidual() {
            return rnorm;
        }
    }

    /** Key for the exception context. */
    private static final String OPERATOR = "operator";

    /** Key for the exception context. */
    private static final String THRESHOLD = "threshold";

    /** Key for the exception context. */
    private static final String VECTOR = "vector";

    /** Key for the exception context. */
    private static final String VECTOR1 = "vector1";

    /** Key for the exception context. */
    private static final String VECTOR2 = "vector2";

    /** {@code true} if symmetry of matrix and conditioner must be checked. */
    private final boolean check;

    /**
     * The value of the custom tolerance &delta; for the default stopping
     * criterion.
     */
    private final double delta;

    /**
     * Creates a new instance of this class, with <a href="#stopcrit">default
     * stopping criterion</a>. Note that setting {@code check} to {@code true}
     * entails an extra matrix-vector product in the initial phase.
     *
     * @param maxIterations the maximum number of iterations
     * @param delta the &delta; parameter for the default stopping criterion
     * @param check {@code true} if self-adjointedness of both matrix and
     * preconditioner should be checked
     */
    public SymmLQ(final int maxIterations, final double delta,
                  final boolean check) {
        super(maxIterations);
        this.delta = delta;
        this.check = check;
    }

    /**
     * Creates a new instance of this class, with <a href="#stopcrit">default
     * stopping criterion</a> and custom iteration manager. Note that setting
     * {@code check} to {@code true} entails an extra matrix-vector product in
     * the initial phase.
     *
     * @param manager the custom iteration manager
     * @param delta the &delta; parameter for the default stopping criterion
     * @param check {@code true} if self-adjointedness of both matrix and
     * preconditioner should be checked
     */
    public SymmLQ(final IterationManager manager, final double delta,
                  final boolean check) {
        super(manager);
        this.delta = delta;
        this.check = check;
    }

    /**
     * Returns {@code true} if symmetry of the matrix, and symmetry as well as
     * positive definiteness of the preconditioner should be checked.
     *
     * @return {@code true} if the tests are to be performed
     */
    public final boolean getCheck() {
        return check;
    }

    /**
     * {@inheritDoc}
     *
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} or {@code m} is not self-adjoint
     * @throws NonPositiveDefiniteOperatorException if {@code m} is not
     * positive definite
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    @Override
    public RealVector solve(final RealLinearOperator a,
        final RealLinearOperator m, final RealVector b) throws
        NullArgumentException, NonSquareOperatorException,
        DimensionMismatchException, MaxCountExceededException,
        NonSelfAdjointOperatorException, NonPositiveDefiniteOperatorException,
        IllConditionedOperatorException {
        MathUtils.checkNotNull(a);
        final RealVector x = new ArrayRealVector(a.getColumnDimension());
        return solveInPlace(a, m, b, x, false, 0.);
    }

    /**
     * Returns an estimate of the solution to the linear system (A - shift
     * &middot; I) &middot; x = b.
     * <p>
     * If the solution x is expected to contain a large multiple of {@code b}
     * (as in Rayleigh-quotient iteration), then better precision may be
     * achieved with {@code goodb} set to {@code true}; this however requires an
     * extra call to the preconditioner.
     * </p>
     * <p>
     * {@code shift} should be zero if the system A &middot; x = b is to be
     * solved. Otherwise, it could be an approximation to an eigenvalue of A,
     * such as the Rayleigh quotient b<sup>T</sup> &middot; A &middot; b /
     * (b<sup>T</sup> &middot; b) corresponding to the vector b. If b is
     * sufficiently like an eigenvector corresponding to an eigenvalue near
     * shift, then the computed x may have very large components. When
     * normalized, x may be closer to an eigenvector than b.
     * </p>
     *
     * @param a the linear operator A of the system
     * @param m the preconditioner, M (can be {@code null})
     * @param b the right-hand side vector
     * @param goodb usually {@code false}, except if {@code x} is expected to
     * contain a large multiple of {@code b}
     * @param shift the amount to be subtracted to all diagonal elements of A
     * @return a reference to {@code x} (shallow copy)
     * @throws NullArgumentException if one of the parameters is {@code null}
     * @throws NonSquareOperatorException if {@code a} or {@code m} is not square
     * @throws DimensionMismatchException if {@code m} or {@code b} have dimensions
     * inconsistent with {@code a}
     * @throws MaxCountExceededException at exhaustion of the iteration count,
     * unless a custom
     * {@link org.apache.commons.math3.util.Incrementor.MaxCountExceededCallback callback}
     * has been set at construction of the {@link IterationManager}
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} or {@code m} is not self-adjoint
     * @throws NonPositiveDefiniteOperatorException if {@code m} is not
     * positive definite
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    public RealVector solve(final RealLinearOperator a,
        final RealLinearOperator m, final RealVector b, final boolean goodb,
        final double shift) throws NullArgumentException,
        NonSquareOperatorException, DimensionMismatchException,
        MaxCountExceededException, NonSelfAdjointOperatorException,
        NonPositiveDefiniteOperatorException, IllConditionedOperatorException {
        MathUtils.checkNotNull(a);
        final RealVector x = new ArrayRealVector(a.getColumnDimension());
        return solveInPlace(a, m, b, x, goodb, shift);
    }

    /**
     * {@inheritDoc}
     *
     * @param x not meaningful in this implementation; should not be considered
     * as an initial guess (<a href="#initguess">more</a>)
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} or {@code m} is not self-adjoint
     * @throws NonPositiveDefiniteOperatorException if {@code m} is not positive
     * definite
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    @Override
    public RealVector solve(final RealLinearOperator a,
        final RealLinearOperator m, final RealVector b, final RealVector x)
        throws NullArgumentException, NonSquareOperatorException,
        DimensionMismatchException, NonSelfAdjointOperatorException,
        NonPositiveDefiniteOperatorException, IllConditionedOperatorException,
        MaxCountExceededException {
        MathUtils.checkNotNull(x);
        return solveInPlace(a, m, b, x.copy(), false, 0.);
    }

    /**
     * {@inheritDoc}
     *
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} is not self-adjoint
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    @Override
    public RealVector solve(final RealLinearOperator a, final RealVector b)
        throws NullArgumentException, NonSquareOperatorException,
        DimensionMismatchException, NonSelfAdjointOperatorException,
        IllConditionedOperatorException, MaxCountExceededException {
        MathUtils.checkNotNull(a);
        final RealVector x = new ArrayRealVector(a.getColumnDimension());
        x.set(0.);
        return solveInPlace(a, null, b, x, false, 0.);
    }

    /**
     * Returns the solution to the system (A - shift &middot; I) &middot; x = b.
     * <p>
     * If the solution x is expected to contain a large multiple of {@code b}
     * (as in Rayleigh-quotient iteration), then better precision may be
     * achieved with {@code goodb} set to {@code true}.
     * </p>
     * <p>
     * {@code shift} should be zero if the system A &middot; x = b is to be
     * solved. Otherwise, it could be an approximation to an eigenvalue of A,
     * such as the Rayleigh quotient b<sup>T</sup> &middot; A &middot; b /
     * (b<sup>T</sup> &middot; b) corresponding to the vector b. If b is
     * sufficiently like an eigenvector corresponding to an eigenvalue near
     * shift, then the computed x may have very large components. When
     * normalized, x may be closer to an eigenvector than b.
     * </p>
     *
     * @param a the linear operator A of the system
     * @param b the right-hand side vector
     * @param goodb usually {@code false}, except if {@code x} is expected to
     * contain a large multiple of {@code b}
     * @param shift the amount to be subtracted to all diagonal elements of A
     * @return a reference to {@code x}
     * @throws NullArgumentException if one of the parameters is {@code null}
     * @throws NonSquareOperatorException if {@code a} is not square
     * @throws DimensionMismatchException if {@code b} has dimensions
     * inconsistent with {@code a}
     * @throws MaxCountExceededException at exhaustion of the iteration count,
     * unless a custom
     * {@link org.apache.commons.math3.util.Incrementor.MaxCountExceededCallback callback}
     * has been set at construction of the {@link IterationManager}
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} is not self-adjoint
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    public RealVector solve(final RealLinearOperator a, final RealVector b,
        final boolean goodb, final double shift) throws NullArgumentException,
        NonSquareOperatorException, DimensionMismatchException,
        NonSelfAdjointOperatorException, IllConditionedOperatorException,
        MaxCountExceededException {
        MathUtils.checkNotNull(a);
        final RealVector x = new ArrayRealVector(a.getColumnDimension());
        return solveInPlace(a, null, b, x, goodb, shift);
    }

    /**
     * {@inheritDoc}
     *
     * @param x not meaningful in this implementation; should not be considered
     * as an initial guess (<a href="#initguess">more</a>)
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} is not self-adjoint
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    @Override
    public RealVector solve(final RealLinearOperator a, final RealVector b,
        final RealVector x) throws NullArgumentException,
        NonSquareOperatorException, DimensionMismatchException,
        NonSelfAdjointOperatorException, IllConditionedOperatorException,
        MaxCountExceededException {
        MathUtils.checkNotNull(x);
        return solveInPlace(a, null, b, x.copy(), false, 0.);
    }

    /**
     * {@inheritDoc}
     *
     * @param x the vector to be updated with the solution; {@code x} should
     * not be considered as an initial guess (<a href="#initguess">more</a>)
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} or {@code m} is not self-adjoint
     * @throws NonPositiveDefiniteOperatorException if {@code m} is not
     * positive definite
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    @Override
    public RealVector solveInPlace(final RealLinearOperator a,
        final RealLinearOperator m, final RealVector b, final RealVector x)
        throws NullArgumentException, NonSquareOperatorException,
        DimensionMismatchException, NonSelfAdjointOperatorException,
        NonPositiveDefiniteOperatorException, IllConditionedOperatorException,
        MaxCountExceededException {
        return solveInPlace(a, m, b, x, false, 0.);
    }

    /**
     * Returns an estimate of the solution to the linear system (A - shift
     * &middot; I) &middot; x = b. The solution is computed in-place.
     * <p>
     * If the solution x is expected to contain a large multiple of {@code b}
     * (as in Rayleigh-quotient iteration), then better precision may be
     * achieved with {@code goodb} set to {@code true}; this however requires an
     * extra call to the preconditioner.
     * </p>
     * <p>
     * {@code shift} should be zero if the system A &middot; x = b is to be
     * solved. Otherwise, it could be an approximation to an eigenvalue of A,
     * such as the Rayleigh quotient b<sup>T</sup> &middot; A &middot; b /
     * (b<sup>T</sup> &middot; b) corresponding to the vector b. If b is
     * sufficiently like an eigenvector corresponding to an eigenvalue near
     * shift, then the computed x may have very large components. When
     * normalized, x may be closer to an eigenvector than b.
     * </p>
     *
     * @param a the linear operator A of the system
     * @param m the preconditioner, M (can be {@code null})
     * @param b the right-hand side vector
     * @param x the vector to be updated with the solution; {@code x} should
     * not be considered as an initial guess (<a href="#initguess">more</a>)
     * @param goodb usually {@code false}, except if {@code x} is expected to
     * contain a large multiple of {@code b}
     * @param shift the amount to be subtracted to all diagonal elements of A
     * @return a reference to {@code x} (shallow copy).
     * @throws NullArgumentException if one of the parameters is {@code null}
     * @throws NonSquareOperatorException if {@code a} or {@code m} is not square
     * @throws DimensionMismatchException if {@code m}, {@code b} or {@code x}
     * have dimensions inconsistent with {@code a}.
     * @throws MaxCountExceededException at exhaustion of the iteration count,
     * unless a custom
     * {@link org.apache.commons.math3.util.Incrementor.MaxCountExceededCallback callback}
     * has been set at construction of the {@link IterationManager}
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} or {@code m} is not self-adjoint
     * @throws NonPositiveDefiniteOperatorException if {@code m} is not positive
     * definite
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    public RealVector solveInPlace(final RealLinearOperator a,
        final RealLinearOperator m, final RealVector b,
        final RealVector x, final boolean goodb, final double shift)
        throws NullArgumentException, NonSquareOperatorException,
        DimensionMismatchException, NonSelfAdjointOperatorException,
        NonPositiveDefiniteOperatorException, IllConditionedOperatorException,
        MaxCountExceededException {
        checkParameters(a, m, b, x);

        final IterationManager manager = getIterationManager();
        /* Initialization counts as an iteration. */
        manager.resetIterationCount();
        manager.incrementIterationCount();

        final State state;
        state = new State(a, m, b, goodb, shift, delta, check);
        state.init();
        state.refineSolution(x);
        IterativeLinearSolverEvent event;
        event = new DefaultIterativeLinearSolverEvent(this,
                                                      manager.getIterations(),
                                                      x,
                                                      b,
                                                      state.getNormOfResidual());
        if (state.bEqualsNullVector()) {
            /* If b = 0 exactly, stop with x = 0. */
            manager.fireTerminationEvent(event);
            return x;
        }
        /* Cause termination if beta is essentially zero. */
        final boolean earlyStop;
        earlyStop = state.betaEqualsZero() || state.hasConverged();
        manager.fireInitializationEvent(event);
        if (!earlyStop) {
            do {
                manager.incrementIterationCount();
                event = new DefaultIterativeLinearSolverEvent(this,
                                                              manager.getIterations(),
                                                              x,
                                                              b,
                                                              state.getNormOfResidual());
                manager.fireIterationStartedEvent(event);
                state.update();
                state.refineSolution(x);
                event = new DefaultIterativeLinearSolverEvent(this,
                                                              manager.getIterations(),
                                                              x,
                                                              b,
                                                              state.getNormOfResidual());
                manager.fireIterationPerformedEvent(event);
            } while (!state.hasConverged());
        }
        event = new DefaultIterativeLinearSolverEvent(this,
                                                      manager.getIterations(),
                                                      x,
                                                      b,
                                                      state.getNormOfResidual());
        manager.fireTerminationEvent(event);
        return x;
    }

    /**
     * {@inheritDoc}
     *
     * @param x the vector to be updated with the solution; {@code x} should
     * not be considered as an initial guess (<a href="#initguess">more</a>)
     * @throws NonSelfAdjointOperatorException if {@link #getCheck()} is
     * {@code true}, and {@code a} is not self-adjoint
     * @throws IllConditionedOperatorException if {@code a} is ill-conditioned
     */
    @Override
    public RealVector solveInPlace(final RealLinearOperator a,
        final RealVector b, final RealVector x) throws NullArgumentException,
        NonSquareOperatorException, DimensionMismatchException,
        NonSelfAdjointOperatorException, IllConditionedOperatorException,
        MaxCountExceededException {
        return solveInPlace(a, null, b, x, false, 0.);
    }
}
