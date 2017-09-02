package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.*;

/**
 * @author Federico Tomassetti
 */
public class TypeInferenceCache {

    private static Map<TypeSolver, IdentityHashMap<LambdaExpr, Map<String, Type>>> typeForLambdaParameters = new HashMap<>();
    private static Map<TypeSolver, IdentityHashMap<LambdaExpr, List<InferenceVariable>>> inferenceVariables = new HashMap<>();

    public static void record(TypeSolver typeSolver, LambdaExpr lambdaExpr, String paramName, Type type) {
        if (!typeForLambdaParameters.containsKey(typeSolver)) {
            typeForLambdaParameters.put(typeSolver, new IdentityHashMap<>());
        }
        if (!typeForLambdaParameters.get(typeSolver).containsKey(lambdaExpr)) {
            typeForLambdaParameters.get(typeSolver).put(lambdaExpr, new HashMap<>());
        }
        typeForLambdaParameters.get(typeSolver).get(lambdaExpr).put(paramName, type);
    }

    public static Optional<Type> retrieve(TypeSolver typeSolver, LambdaExpr lambdaExpr, String paramName) {
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
