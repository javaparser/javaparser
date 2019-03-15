package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Finds the type that all types share.
 */
public class CommonTypeLocator {
    public Optional<ResolvedReferenceType> findCommonType(List<ResolvedReferenceType> elements) {
        if (elements.isEmpty()) {
            throw new IllegalStateException("This method needs at least one type.");
        }
        Optional<List<ResolvedReferenceType>> reduce = elements.stream()
                .map(ResolvedType::asReferenceType)
                .map(ResolvedReferenceType::getAllAncestors)
                .reduce((a, b) -> {
                    List<ResolvedReferenceType> common = new ArrayList<>(a);
                    common.retainAll(b);
                    return common;
                });
        return reduce.orElse(new ArrayList<>()).stream().findFirst();
    }
    
}
