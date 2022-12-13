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

package com.github.javaparser.symbolsolver.resolution.typeinference.bounds;

import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariableSubstitution;

import java.util.List;
import java.util.Set;

/**
 * Capture(G&lt;A1, ..., An&gt;): The variables α1, ..., αn represent the result of capture conversion (§5.1.10)
 * applied to G&lt;A1, ..., An&gt; (where A1, ..., An may be types or wildcards and may mention inference variables).
 *
 * @author Federico Tomassetti
 */
public class CapturesBound extends Bound {
    private List<InferenceVariable> inferenceVariables;
    private List<ResolvedType> typesOrWildcards;

    public CapturesBound(List<InferenceVariable> inferenceVariables, List<ResolvedType> typesOrWildcards) {
        this.inferenceVariables = inferenceVariables;
        this.typesOrWildcards = typesOrWildcards;
    }

    @Override
    public boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<InferenceVariable> usedInferenceVariables() {
        throw new UnsupportedOperationException();
    }

    public List<InferenceVariable> getInferenceVariables() {
        return inferenceVariables;
    }

    public List<ResolvedType> getTypesOrWildcards() {
        return typesOrWildcards;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CapturesBound that = (CapturesBound) o;

        if (!inferenceVariables.equals(that.inferenceVariables)) return false;
        return typesOrWildcards.equals(that.typesOrWildcards);
    }

    @Override
    public int hashCode() {
        int result = inferenceVariables.hashCode();
        result = 31 * result + typesOrWildcards.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "CapturesBound{" +
                "inferenceVariables=" + inferenceVariables +
                ", typesOrWildcards=" + typesOrWildcards +
                '}';
    }
}
