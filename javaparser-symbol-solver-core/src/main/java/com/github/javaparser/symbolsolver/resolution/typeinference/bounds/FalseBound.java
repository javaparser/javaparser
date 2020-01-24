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

import com.github.javaparser.symbolsolver.resolution.typeinference.Bound;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariable;
import com.github.javaparser.symbolsolver.resolution.typeinference.InferenceVariableSubstitution;

import java.util.Collections;
import java.util.Set;

/**
 * No valid choice of inference variables exists.
 *
 * @author Federico Tomassetti
 */
public class FalseBound extends Bound {

    private static FalseBound INSTANCE = new FalseBound();

    private FalseBound() {

    }

    public static FalseBound getInstance() {
        return INSTANCE;
    }

    @Override
    public String toString() {
        return "FalseBound{}";
    }

    @Override
    public boolean isSatisfied(InferenceVariableSubstitution inferenceVariableSubstitution) {
        return false;
    }

    @Override
    public Set<InferenceVariable> usedInferenceVariables() {
        return Collections.emptySet();
    }
}
