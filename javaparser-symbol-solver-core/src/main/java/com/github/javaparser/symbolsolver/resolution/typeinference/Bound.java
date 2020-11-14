/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.FalseBound;

import java.util.Optional;
import java.util.Set;

/**
 * Bounds are defined for Inference Variables.
 *
 * @author Federico Tomassetti
 */
public abstract class Bound {

    ///
    /// Creation of bounds
    ///

    static Bound falseBound() {
        return FalseBound.getInstance();
    }

    ///
    /// Satisfiability
    ///

    /**
     * A bound is satisfied by an inference variable substitution if, after applying the substitution,
     * the assertion is true.
     */
    public abstract boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution);

    ///
    /// Classification of bounds
    ///

    /**
     * Given a bound of the form α = T or T = α, we say T is an instantiation of α.
     *
     * Return empty if it is not an instantiation. Otherwise it returns the variable of which this is an
     * instantiation.
     */
    public Optional<Instantiation> isAnInstantiation() {
        return Optional.empty();
    }

    boolean isAnInstantiationFor(InferenceVariable v) {
        return isAnInstantiation().isPresent() && isAnInstantiation().get().getInferenceVariable().equals(v);
    }

    /**
     * Given a bound of the form α &lt;: T, we say T is a proper upper bound of α.
     *
     * Return empty if it is not a proper upper bound. Otherwise it returns the variable of which this is an
     * proper upper bound.
     */
    public Optional<ProperUpperBound> isProperUpperBound() {
        return Optional.empty();
    }

    /**
     * Given a bound of the form T &lt;: α, we say T is a proper lower bound of α.
     *
     * Return empty if it is not a proper lower bound. Otherwise it returns the variable of which this is an
     * proper lower bound.
     */
    public Optional<ProperLowerBound> isProperLowerBound() {
        return Optional.empty();
    }

    Optional<ProperLowerBound> isProperLowerBoundFor(InferenceVariable inferenceVariable) {
        Optional<ProperLowerBound> partial = isProperLowerBound();
        if (partial.isPresent() && partial.get().getInferenceVariable().equals(inferenceVariable)) {
            return partial;
        } else {
            return Optional.empty();
        }
    }

    Optional<ProperUpperBound> isProperUpperBoundFor(InferenceVariable inferenceVariable) {
        Optional<ProperUpperBound> partial = isProperUpperBound();
        if (partial.isPresent() && partial.get().getInferenceVariable().equals(inferenceVariable)) {
            return partial;
        } else {
            return Optional.empty();
        }
    }

    /**
     * Other bounds relate two inference variables, or an inference variable to a type that contains inference
     * variables. Such bounds, of the form S = T or S &lt;: T, are called dependencies.
     */
    public boolean isADependency() {
        return false;
    }

    boolean isThrowsBoundOn(InferenceVariable inferenceVariable) {
        return false;
    }

    ///
    /// Other methods
    ///

    public abstract Set<InferenceVariable> usedInferenceVariables();
}
