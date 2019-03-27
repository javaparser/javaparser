package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedUnionType;
import com.github.javaparser.resolution.types.ResolvedVoidType;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Stream;

/**
 * Invents a type for a piece of code that can result in several types.
 * <ul>
 * <li>If no types are found, the result is void.
 * <li>If one type is found, the result is that type.
 * <li>If multiple types are found, the result is a union of those types.
 * </ul>
 */
public final class MultipleResultTypesLogic {

    public ResolvedType findResultType(Stream<ResolvedType> types) {
        Map<String, ResolvedType> resultTypes = new HashMap<>();
        types.forEach(t -> resultTypes.put(t.describe(), t));
        int amountOfTypes = resultTypes.size();
        switch (amountOfTypes) {
            case 0:
                return ResolvedVoidType.INSTANCE;
            case 1:
                return resultTypes.values().iterator().next();
            default:
                return new ResolvedUnionType(resultTypes.values());
        }
    }

    public <T extends Node> ResolvedType findResultType(Node node, Class<T> returningType, Function<T, ResolvedType> resolver) {
        return findResultType(node.findAll(returningType).stream().map(resolver));
    }
}
