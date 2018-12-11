package com.github.javaparser.symbolsolver.core.resolution;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.List;

public interface TypeVariableResolutionCapability {
	MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes);
}
