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

package org.apache.commons.math3.analysis;

import org.apache.commons.math3.analysis.differentiation.DerivativeStructure;
import org.apache.commons.math3.analysis.differentiation.MultivariateDifferentiableFunction;
import org.apache.commons.math3.analysis.differentiation.MultivariateDifferentiableVectorFunction;
import org.apache.commons.math3.analysis.differentiation.UnivariateDifferentiableFunction;
import org.apache.commons.math3.analysis.function.Identity;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Utilities for manipulating function objects.
 *
 * @since 3.0
 */
public class FunctionUtils {
    /**
     * Class only contains static methods.
     */
    private FunctionUtils() {}

    /**
     * Composes functions.
     * <p>
     * The functions in the argument list are composed sequentially, in the
     * given order.  For example, compose(f1,f2,f3) acts like f1(f2(f3(x))).</p>
     *
     * @param f List of functions.
     * @return the composite function.
     */
    public static UnivariateFunction compose(final UnivariateFunction ... f) {
        return new UnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                double r = x;
                for (int i = f.length - 1; i >= 0; i--) {
                    r = f[i].value(r);
                }
                return r;
            }
        };
    }

    /**
     * Composes functions.
     * <p>
     * The functions in the argument list are composed sequentially, in the
     * given order.  For example, compose(f1,f2,f3) acts like f1(f2(f3(x))).</p>
     *
     * @param f List of functions.
     * @return the composite function.
     * @since 3.1
     */
    public static UnivariateDifferentiableFunction compose(final UnivariateDifferentiableFunction ... f) {
        return new UnivariateDifferentiableFunction() {

            /** {@inheritDoc} */
            public double value(final double t) {
                double r = t;
                for (int i = f.length - 1; i >= 0; i--) {
                    r = f[i].value(r);
                }
                return r;
            }

            /** {@inheritDoc} */
            public DerivativeStructure value(final DerivativeStructure t) {
                DerivativeStructure r = t;
                for (int i = f.length - 1; i >= 0; i--) {
                    r = f[i].value(r);
                }
                return r;
            }

        };
    }

    /**
     * Composes functions.
     * <p>
     * The functions in the argument list are composed sequentially, in the
     * given order.  For example, compose(f1,f2,f3) acts like f1(f2(f3(x))).</p>
     *
     * @param f List of functions.
     * @return the composite function.
     * @deprecated as of 3.1 replaced by {@link #compose(UnivariateDifferentiableFunction...)}
     */
    @Deprecated
    public static DifferentiableUnivariateFunction compose(final DifferentiableUnivariateFunction ... f) {
        return new DifferentiableUnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                double r = x;
                for (int i = f.length - 1; i >= 0; i--) {
                    r = f[i].value(r);
                }
                return r;
            }

            /** {@inheritDoc} */
            public UnivariateFunction derivative() {
                return new UnivariateFunction() {
                    /** {@inheritDoc} */
                    public double value(double x) {
                        double p = 1;
                        double r = x;
                        for (int i = f.length - 1; i >= 0; i--) {
                            p *= f[i].derivative().value(r);
                            r = f[i].value(r);
                        }
                        return p;
                    }
                };
            }
        };
    }

    /**
     * Adds functions.
     *
     * @param f List of functions.
     * @return a function that computes the sum of the functions.
     */
    public static UnivariateFunction add(final UnivariateFunction ... f) {
        return new UnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                double r = f[0].value(x);
                for (int i = 1; i < f.length; i++) {
                    r += f[i].value(x);
                }
                return r;
            }
        };
    }

    /**
     * Adds functions.
     *
     * @param f List of functions.
     * @return a function that computes the sum of the functions.
     * @since 3.1
     */
    public static UnivariateDifferentiableFunction add(final UnivariateDifferentiableFunction ... f) {
        return new UnivariateDifferentiableFunction() {

            /** {@inheritDoc} */
            public double value(final double t) {
                double r = f[0].value(t);
                for (int i = 1; i < f.length; i++) {
                    r += f[i].value(t);
                }
                return r;
            }

            /** {@inheritDoc}
             * @throws DimensionMismatchException if functions are not consistent with each other
             */
            public DerivativeStructure value(final DerivativeStructure t)
                throws DimensionMismatchException {
                DerivativeStructure r = f[0].value(t);
                for (int i = 1; i < f.length; i++) {
                    r = r.add(f[i].value(t));
                }
                return r;
            }

        };
    }

    /**
     * Adds functions.
     *
     * @param f List of functions.
     * @return a function that computes the sum of the functions.
     * @deprecated as of 3.1 replaced by {@link #add(UnivariateDifferentiableFunction...)}
     */
    @Deprecated
    public static DifferentiableUnivariateFunction add(final DifferentiableUnivariateFunction ... f) {
        return new DifferentiableUnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                double r = f[0].value(x);
                for (int i = 1; i < f.length; i++) {
                    r += f[i].value(x);
                }
                return r;
            }

            /** {@inheritDoc} */
            public UnivariateFunction derivative() {
                return new UnivariateFunction() {
                    /** {@inheritDoc} */
                    public double value(double x) {
                        double r = f[0].derivative().value(x);
                        for (int i = 1; i < f.length; i++) {
                            r += f[i].derivative().value(x);
                        }
                        return r;
                    }
                };
            }
        };
    }

    /**
     * Multiplies functions.
     *
     * @param f List of functions.
     * @return a function that computes the product of the functions.
     */
    public static UnivariateFunction multiply(final UnivariateFunction ... f) {
        return new UnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                double r = f[0].value(x);
                for (int i = 1; i < f.length; i++) {
                    r *= f[i].value(x);
                }
                return r;
            }
        };
    }

    /**
     * Multiplies functions.
     *
     * @param f List of functions.
     * @return a function that computes the product of the functions.
     * @since 3.1
     */
    public static UnivariateDifferentiableFunction multiply(final UnivariateDifferentiableFunction ... f) {
        return new UnivariateDifferentiableFunction() {

            /** {@inheritDoc} */
            public double value(final double t) {
                double r = f[0].value(t);
                for (int i = 1; i < f.length; i++) {
                    r  *= f[i].value(t);
                }
                return r;
            }

            /** {@inheritDoc} */
            public DerivativeStructure value(final DerivativeStructure t) {
                DerivativeStructure r = f[0].value(t);
                for (int i = 1; i < f.length; i++) {
                    r = r.multiply(f[i].value(t));
                }
                return r;
            }

        };
    }

    /**
     * Multiplies functions.
     *
     * @param f List of functions.
     * @return a function that computes the product of the functions.
     * @deprecated as of 3.1 replaced by {@link #multiply(UnivariateDifferentiableFunction...)}
     */
    @Deprecated
    public static DifferentiableUnivariateFunction multiply(final DifferentiableUnivariateFunction ... f) {
        return new DifferentiableUnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                double r = f[0].value(x);
                for (int i = 1; i < f.length; i++) {
                    r *= f[i].value(x);
                }
                return r;
            }

            /** {@inheritDoc} */
            public UnivariateFunction derivative() {
                return new UnivariateFunction() {
                    /** {@inheritDoc} */
                    public double value(double x) {
                        double sum = 0;
                        for (int i = 0; i < f.length; i++) {
                            double prod = f[i].derivative().value(x);
                            for (int j = 0; j < f.length; j++) {
                                if (i != j) {
                                    prod *= f[j].value(x);
                                }
                            }
                            sum += prod;
                        }
                        return sum;
                    }
                };
            }
        };
    }

    /**
     * Returns the univariate function
     * {@code h(x) = combiner(f(x), g(x)).}
     *
     * @param combiner Combiner function.
     * @param f Function.
     * @param g Function.
     * @return the composite function.
     */
    public static UnivariateFunction combine(final BivariateFunction combiner,
                                             final UnivariateFunction f,
                                             final UnivariateFunction g) {
        return new UnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                return combiner.value(f.value(x), g.value(x));
            }
        };
    }

    /**
     * Returns a MultivariateFunction h(x[]) defined by <pre> <code>
     * h(x[]) = combiner(...combiner(combiner(initialValue,f(x[0])),f(x[1]))...),f(x[x.length-1]))
     * </code></pre>
     *
     * @param combiner Combiner function.
     * @param f Function.
     * @param initialValue Initial value.
     * @return a collector function.
     */
    public static MultivariateFunction collector(final BivariateFunction combiner,
                                                 final UnivariateFunction f,
                                                 final double initialValue) {
        return new MultivariateFunction() {
            /** {@inheritDoc} */
            public double value(double[] point) {
                double result = combiner.value(initialValue, f.value(point[0]));
                for (int i = 1; i < point.length; i++) {
                    result = combiner.value(result, f.value(point[i]));
                }
                return result;
            }
        };
    }

    /**
     * Returns a MultivariateFunction h(x[]) defined by <pre> <code>
     * h(x[]) = combiner(...combiner(combiner(initialValue,x[0]),x[1])...),x[x.length-1])
     * </code></pre>
     *
     * @param combiner Combiner function.
     * @param initialValue Initial value.
     * @return a collector function.
     */
    public static MultivariateFunction collector(final BivariateFunction combiner,
                                                 final double initialValue) {
        return collector(combiner, new Identity(), initialValue);
    }

    /**
     * Creates a unary function by fixing the first argument of a binary function.
     *
     * @param f Binary function.
     * @param fixed value to which the first argument of {@code f} is set.
     * @return the unary function h(x) = f(fixed, x)
     */
    public static UnivariateFunction fix1stArgument(final BivariateFunction f,
                                                    final double fixed) {
        return new UnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                return f.value(fixed, x);
            }
        };
    }
    /**
     * Creates a unary function by fixing the second argument of a binary function.
     *
     * @param f Binary function.
     * @param fixed value to which the second argument of {@code f} is set.
     * @return the unary function h(x) = f(x, fixed)
     */
    public static UnivariateFunction fix2ndArgument(final BivariateFunction f,
                                                    final double fixed) {
        return new UnivariateFunction() {
            /** {@inheritDoc} */
            public double value(double x) {
                return f.value(x, fixed);
            }
        };
    }

    /**
     * Samples the specified univariate real function on the specified interval.
     * <p>
     * The interval is divided equally into {@code n} sections and sample points
     * are taken from {@code min} to {@code max - (max - min) / n}; therefore
     * {@code f} is not sampled at the upper bound {@code max}.</p>
     *
     * @param f Function to be sampled
     * @param min Lower bound of the interval (included).
     * @param max Upper bound of the interval (excluded).
     * @param n Number of sample points.
     * @return the array of samples.
     * @throws NumberIsTooLargeException if the lower bound {@code min} is
     * greater than, or equal to the upper bound {@code max}.
     * @throws NotStrictlyPositiveException if the number of sample points
     * {@code n} is negative.
     */
    public static double[] sample(UnivariateFunction f, double min, double max, int n)
       throws NumberIsTooLargeException, NotStrictlyPositiveException {

        if (n <= 0) {
            throw new NotStrictlyPositiveException(
                    LocalizedFormats.NOT_POSITIVE_NUMBER_OF_SAMPLES,
                    Integer.valueOf(n));
        }
        if (min >= max) {
            throw new NumberIsTooLargeException(min, max, false);
        }

        final double[] s = new double[n];
        final double h = (max - min) / n;
        for (int i = 0; i < n; i++) {
            s[i] = f.value(min + i * h);
        }
        return s;
    }

    /**
     * Convert a {@link UnivariateDifferentiableFunction} into a {@link DifferentiableUnivariateFunction}.
     *
     * @param f function to convert
     * @return converted function
     * @deprecated this conversion method is temporary in version 3.1, as the {@link
     * DifferentiableUnivariateFunction} interface itself is deprecated
     */
    @Deprecated
    public static DifferentiableUnivariateFunction toDifferentiableUnivariateFunction(final UnivariateDifferentiableFunction f) {
        return new DifferentiableUnivariateFunction() {

            /** {@inheritDoc} */
            public double value(final double x) {
                return f.value(x);
            }

            /** {@inheritDoc} */
            public UnivariateFunction derivative() {
                return new UnivariateFunction() {
                    /** {@inheritDoc} */
                    public double value(final double x) {
                        return f.value(new DerivativeStructure(1, 1, 0, x)).getPartialDerivative(1);
                    }
                };
            }

        };
    }

    /**
     * Convert a {@link DifferentiableUnivariateFunction} into a {@link UnivariateDifferentiableFunction}.
     * <p>
     * Note that the converted function is able to handle {@link DerivativeStructure} up to order one.
     * If the function is called with higher order, a {@link NumberIsTooLargeException} is thrown.
     * </p>
     * @param f function to convert
     * @return converted function
     * @deprecated this conversion method is temporary in version 3.1, as the {@link
     * DifferentiableUnivariateFunction} interface itself is deprecated
     */
    @Deprecated
    public static UnivariateDifferentiableFunction toUnivariateDifferential(final DifferentiableUnivariateFunction f) {
        return new UnivariateDifferentiableFunction() {

            /** {@inheritDoc} */
            public double value(final double x) {
                return f.value(x);
            }

            /** {@inheritDoc}
             * @exception NumberIsTooLargeException if derivation order is greater than 1
             */
            public DerivativeStructure value(final DerivativeStructure t)
                throws NumberIsTooLargeException {
                switch (t.getOrder()) {
                    case 0 :
                        return new DerivativeStructure(t.getFreeParameters(), 0, f.value(t.getValue()));
                    case 1 : {
                        final int parameters = t.getFreeParameters();
                        final double[] derivatives = new double[parameters + 1];
                        derivatives[0] = f.value(t.getValue());
                        final double fPrime = f.derivative().value(t.getValue());
                        int[] orders = new int[parameters];
                        for (int i = 0; i < parameters; ++i) {
                            orders[i] = 1;
                            derivatives[i + 1] = fPrime * t.getPartialDerivative(orders);
                            orders[i] = 0;
                        }
                        return new DerivativeStructure(parameters, 1, derivatives);
                    }
                    default :
                        throw new NumberIsTooLargeException(t.getOrder(), 1, true);
                }
            }

        };
    }

    /**
     * Convert a {@link MultivariateDifferentiableFunction} into a {@link DifferentiableMultivariateFunction}.
     *
     * @param f function to convert
     * @return converted function
     * @deprecated this conversion method is temporary in version 3.1, as the {@link
     * DifferentiableMultivariateFunction} interface itself is deprecated
     */
    @Deprecated
    public static DifferentiableMultivariateFunction toDifferentiableMultivariateFunction(final MultivariateDifferentiableFunction f) {
        return new DifferentiableMultivariateFunction() {

            /** {@inheritDoc} */
            public double value(final double[] x) {
                return f.value(x);
            }

            /** {@inheritDoc} */
            public MultivariateFunction partialDerivative(final int k) {
                return new MultivariateFunction() {
                    /** {@inheritDoc} */
                    public double value(final double[] x) {

                        final int n = x.length;

                        // delegate computation to underlying function
                        final DerivativeStructure[] dsX = new DerivativeStructure[n];
                        for (int i = 0; i < n; ++i) {
                            if (i == k) {
                                dsX[i] = new DerivativeStructure(1, 1, 0, x[i]);
                            } else {
                                dsX[i] = new DerivativeStructure(1, 1, x[i]);
                            }
                        }
                        final DerivativeStructure y = f.value(dsX);

                        // extract partial derivative
                        return y.getPartialDerivative(1);

                    }
                };
            }

            /** {@inheritDoc} */
            public MultivariateVectorFunction gradient() {
                return new MultivariateVectorFunction() {
                    /** {@inheritDoc} */
                    public double[] value(final double[] x) {

                        final int n = x.length;

                        // delegate computation to underlying function
                        final DerivativeStructure[] dsX = new DerivativeStructure[n];
                        for (int i = 0; i < n; ++i) {
                            dsX[i] = new DerivativeStructure(n, 1, i, x[i]);
                        }
                        final DerivativeStructure y = f.value(dsX);

                        // extract gradient
                        final double[] gradient = new double[n];
                        final int[] orders = new int[n];
                        for (int i = 0; i < n; ++i) {
                            orders[i]   = 1;
                            gradient[i] = y.getPartialDerivative(orders);
                            orders[i]   = 0;
                        }

                        return gradient;

                    }
                };
            }

        };
    }

    /**
     * Convert a {@link DifferentiableMultivariateFunction} into a {@link MultivariateDifferentiableFunction}.
     * <p>
     * Note that the converted function is able to handle {@link DerivativeStructure} elements
     * that all have the same number of free parameters and order, and with order at most 1.
     * If the function is called with inconsistent numbers of free parameters or higher order, a
     * {@link DimensionMismatchException} or a {@link NumberIsTooLargeException} will be thrown.
     * </p>
     * @param f function to convert
     * @return converted function
     * @deprecated this conversion method is temporary in version 3.1, as the {@link
     * DifferentiableMultivariateFunction} interface itself is deprecated
     */
    @Deprecated
    public static MultivariateDifferentiableFunction toMultivariateDifferentiableFunction(final DifferentiableMultivariateFunction f) {
        return new MultivariateDifferentiableFunction() {

            /** {@inheritDoc} */
            public double value(final double[] x) {
                return f.value(x);
            }

            /** {@inheritDoc}
             * @exception NumberIsTooLargeException if derivation order is higher than 1
             * @exception DimensionMismatchException if numbers of free parameters are inconsistent
             */
            public DerivativeStructure value(final DerivativeStructure[] t)
                throws DimensionMismatchException, NumberIsTooLargeException {

                // check parameters and orders limits
                final int parameters = t[0].getFreeParameters();
                final int order      = t[0].getOrder();
                final int n          = t.length;
                if (order > 1) {
                    throw new NumberIsTooLargeException(order, 1, true);
                }

                // check all elements in the array are consistent
                for (int i = 0; i < n; ++i) {
                    if (t[i].getFreeParameters() != parameters) {
                        throw new DimensionMismatchException(t[i].getFreeParameters(), parameters);
                    }

                    if (t[i].getOrder() != order) {
                        throw new DimensionMismatchException(t[i].getOrder(), order);
                    }
                }

                // delegate computation to underlying function
                final double[] point = new double[n];
                for (int i = 0; i < n; ++i) {
                    point[i] = t[i].getValue();
                }
                final double value      = f.value(point);
                final double[] gradient = f.gradient().value(point);

                // merge value and gradient into one DerivativeStructure
                final double[] derivatives = new double[parameters + 1];
                derivatives[0] = value;
                final int[] orders = new int[parameters];
                for (int i = 0; i < parameters; ++i) {
                    orders[i] = 1;
                    for (int j = 0; j < n; ++j) {
                        derivatives[i + 1] += gradient[j] * t[j].getPartialDerivative(orders);
                    }
                    orders[i] = 0;
                }

                return new DerivativeStructure(parameters, order, derivatives);

            }

        };
    }

    /**
     * Convert a {@link MultivariateDifferentiableVectorFunction} into a {@link DifferentiableMultivariateVectorFunction}.
     *
     * @param f function to convert
     * @return converted function
     * @deprecated this conversion method is temporary in version 3.1, as the {@link
     * DifferentiableMultivariateVectorFunction} interface itself is deprecated
     */
    @Deprecated
    public static DifferentiableMultivariateVectorFunction toDifferentiableMultivariateVectorFunction(final MultivariateDifferentiableVectorFunction f) {
        return new DifferentiableMultivariateVectorFunction() {

            /** {@inheritDoc} */
            public double[] value(final double[] x) {
                return f.value(x);
            }

            /** {@inheritDoc} */
            public MultivariateMatrixFunction jacobian() {
                return new MultivariateMatrixFunction() {
                    /** {@inheritDoc} */
                    public double[][] value(final double[] x) {

                        final int n = x.length;

                        // delegate computation to underlying function
                        final DerivativeStructure[] dsX = new DerivativeStructure[n];
                        for (int i = 0; i < n; ++i) {
                            dsX[i] = new DerivativeStructure(n, 1, i, x[i]);
                        }
                        final DerivativeStructure[] y = f.value(dsX);

                        // extract Jacobian
                        final double[][] jacobian = new double[y.length][n];
                        final int[] orders = new int[n];
                        for (int i = 0; i < y.length; ++i) {
                            for (int j = 0; j < n; ++j) {
                                orders[j]      = 1;
                                jacobian[i][j] = y[i].getPartialDerivative(orders);
                                orders[j]      = 0;
                            }
                        }

                        return jacobian;

                    }
                };
            }

        };
    }

    /**
     * Convert a {@link DifferentiableMultivariateVectorFunction} into a {@link MultivariateDifferentiableVectorFunction}.
     * <p>
     * Note that the converted function is able to handle {@link DerivativeStructure} elements
     * that all have the same number of free parameters and order, and with order at most 1.
     * If the function is called with inconsistent numbers of free parameters or higher order, a
     * {@link DimensionMismatchException} or a {@link NumberIsTooLargeException} will be thrown.
     * </p>
     * @param f function to convert
     * @return converted function
     * @deprecated this conversion method is temporary in version 3.1, as the {@link
     * DifferentiableMultivariateFunction} interface itself is deprecated
     */
    @Deprecated
    public static MultivariateDifferentiableVectorFunction toMultivariateDifferentiableVectorFunction(final DifferentiableMultivariateVectorFunction f) {
        return new MultivariateDifferentiableVectorFunction() {

            /** {@inheritDoc} */
            public double[] value(final double[] x) {
                return f.value(x);
            }

            /** {@inheritDoc}
             * @exception NumberIsTooLargeException if derivation order is higher than 1
             * @exception DimensionMismatchException if numbers of free parameters are inconsistent
             */
            public DerivativeStructure[] value(final DerivativeStructure[] t)
                throws DimensionMismatchException, NumberIsTooLargeException {

                // check parameters and orders limits
                final int parameters = t[0].getFreeParameters();
                final int order      = t[0].getOrder();
                final int n          = t.length;
                if (order > 1) {
                    throw new NumberIsTooLargeException(order, 1, true);
                }

                // check all elements in the array are consistent
                for (int i = 0; i < n; ++i) {
                    if (t[i].getFreeParameters() != parameters) {
                        throw new DimensionMismatchException(t[i].getFreeParameters(), parameters);
                    }

                    if (t[i].getOrder() != order) {
                        throw new DimensionMismatchException(t[i].getOrder(), order);
                    }
                }

                // delegate computation to underlying function
                final double[] point = new double[n];
                for (int i = 0; i < n; ++i) {
                    point[i] = t[i].getValue();
                }
                final double[] value      = f.value(point);
                final double[][] jacobian = f.jacobian().value(point);

                // merge value and Jacobian into a DerivativeStructure array
                final DerivativeStructure[] merged = new DerivativeStructure[value.length];
                for (int k = 0; k < merged.length; ++k) {
                    final double[] derivatives = new double[parameters + 1];
                    derivatives[0] = value[k];
                    final int[] orders = new int[parameters];
                    for (int i = 0; i < parameters; ++i) {
                        orders[i] = 1;
                        for (int j = 0; j < n; ++j) {
                            derivatives[i + 1] += jacobian[k][j] * t[j].getPartialDerivative(orders);
                        }
                        orders[i] = 0;
                    }
                    merged[k] = new DerivativeStructure(parameters, order, derivatives);
                }

                return merged;

            }

        };
    }

}
