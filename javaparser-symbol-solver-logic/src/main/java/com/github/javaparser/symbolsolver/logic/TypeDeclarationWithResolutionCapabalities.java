package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;

public interface TypeDeclarationWithResolutionCapabalities {

	SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
	                                                       boolean staticOnly, TypeSolver typeSolver);


}
