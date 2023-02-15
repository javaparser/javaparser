/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariableSubstitution;

import java.util.HashSet;
import java.util.Set;

/**
 * The inference variable α appears in a throws clause.
 *
 * A bound of the form throws α is purely informational: it directs resolution to optimize the instantiation of α so
 * that, if possible, it is not a checked exception type.
 *
 * @author Federico Tomassetti
 */
public class ThrowsBound extends Bound {
    private InferenceVariable inferenceVariable;

    public ThrowsBound(InferenceVariable inferenceVariable) {
        this.inferenceVariable = inferenceVariable;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ThrowsBound that = (ThrowsBound) o;

        return inferenceVariable.equals(that.inferenceVariable);
    }

    @Override
    public String toString() {
        return "ThrowsBound{" +
                "inferenceVariable=" + inferenceVariable +
                '}';
    }

    @Override
    public int hashCode() {
        return inferenceVariable.hashCode();
    }

    @Override
    public Set<InferenceVariable> usedInferenceVariables() {
        Set<InferenceVariable> variables = new HashSet<>();
        variables.add(inferenceVariable);
        return variables;
    }

    @Override
    public boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution) {
        throw new UnsupportedOperationException();
    }

    public boolean isThrowsBoundOn(InferenceVariable inferenceVariable) {
        return inferenceVariable.equals(this.inferenceVariable);
    }
}
