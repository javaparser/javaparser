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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.*;

/**
 * @author Federico Tomassetti
 */
public class TypeInferenceCache {

    private static Map<TypeSolver, IdentityHashMap<LambdaExpr, Map<String, ResolvedType>>> typeForLambdaParameters = new HashMap<>();
    private static Map<TypeSolver, IdentityHashMap<LambdaExpr, List<InferenceVariable>>> inferenceVariables = new HashMap<>();

    public static void addRecord(TypeSolver typeSolver, LambdaExpr lambdaExpr, String paramName, ResolvedType type) {
        if (!typeForLambdaParameters.containsKey(typeSolver)) {
            typeForLambdaParameters.put(typeSolver, new IdentityHashMap<>());
        }
        if (!typeForLambdaParameters.get(typeSolver).containsKey(lambdaExpr)) {
            typeForLambdaParameters.get(typeSolver).put(lambdaExpr, new HashMap<>());
        }
        typeForLambdaParameters.get(typeSolver).get(lambdaExpr).put(paramName, type);
    }

    public static Optional<ResolvedType> retrieve(TypeSolver typeSolver, LambdaExpr lambdaExpr, String paramName) {
        if (!typeForLambdaParameters.containsKey(typeSolver)) {
            return Optional.empty();
        }
        if (!typeForLambdaParameters.get(typeSolver).containsKey(lambdaExpr)) {
            return Optional.empty();
        }
        if (!typeForLambdaParameters.get(typeSolver).get(lambdaExpr).containsKey(paramName)) {
            return Optional.empty();
        }
        return Optional.of(typeForLambdaParameters.get(typeSolver).get(lambdaExpr).get(paramName));
    }

    public static void recordInferenceVariables(TypeSolver typeSolver, LambdaExpr lambdaExpr, List<InferenceVariable> _inferenceVariables) {
        if (!inferenceVariables.containsKey(typeSolver)) {
            inferenceVariables.put(typeSolver, new IdentityHashMap<>());
        }
        inferenceVariables.get(typeSolver).put(lambdaExpr, _inferenceVariables);
    }

    public static Optional<List<InferenceVariable>> retrieveInferenceVariables(TypeSolver typeSolver, LambdaExpr lambdaExpr) {
        if (!inferenceVariables.containsKey(typeSolver)) {
            return Optional.empty();
        }
        if (!inferenceVariables.get(typeSolver).containsKey(lambdaExpr)) {
            return Optional.empty();
        }
        return Optional.of(inferenceVariables.get(typeSolver).get(lambdaExpr));
    }
}
