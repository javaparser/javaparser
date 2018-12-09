package com.github.javaparser.symbolsolver.core.resolution;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.List;
import java.util.Optional;

public interface MethodUsageResolutionCapability {
	Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentTypes, Context invocationContext,
	                                         List<ResolvedType> typeParameters);
}
