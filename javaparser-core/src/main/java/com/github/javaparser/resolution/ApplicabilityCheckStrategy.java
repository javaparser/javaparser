package com.github.javaparser.resolution;

import java.util.List;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

/**
 * Strategy for allowing different Implementations of the applicability check done for method resolving.
 * 
 * @author stefanleh
 *
 */
public interface ApplicabilityCheckStrategy {

    /**
     * Checks if a given {@link ResolvedMethodDeclaration} is applicable of the given list of {@link ResolvedType}s.
     * The latter come from resolving the actual parameter types of the method found by JavaParser in the source.
     * 
     * @param method the {@link ResolvedMethodDeclaration} to check for applicability
     * @param name the name of the method
     * @param argumentsTypes the argumenttypes of the method (from parser)
     * @param typeSolver the {@link TypeSolver} to use
     * @param withWildcardTolerance <code>true</code> if wildcards are tolerated, <code>false</code> if not
     * @return <code>true</code> if applicable, <code>false</code> if not
     */
    boolean isApplicable(ResolvedMethodDeclaration method, String name, List<ResolvedType> argumentsTypes,
                         TypeSolver typeSolver,
                         boolean withWildcardTolerance);

}
