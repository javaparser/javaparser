package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.types.ResolvedType;

/**
 * @author Federico Tomassetti
 */
public class ConfilictingGenericTypesException extends RuntimeException {

    public ConfilictingGenericTypesException(ResolvedType formalType, ResolvedType actualType) {
        super(String.format("No matching between %s (formal) and %s (actual)", formalType, actualType));
    }
}
