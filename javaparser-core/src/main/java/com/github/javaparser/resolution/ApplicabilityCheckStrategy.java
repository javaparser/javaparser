package com.github.javaparser.resolution;

import java.util.List;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

public interface ApplicabilityCheckStrategy {

    boolean isApplicable(ResolvedMethodDeclaration method, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, boolean withWildcardTolerance);
    
}
