package com.github.javaparser.symbolsolver.core.resolution;

import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * Allows for an implementing declaration type to support solving for field <i>(symbol)</i> usage.
 */
public interface SymbolResolutionCapability {
	/**
	 * @param name Field / symbol name.
	 * @param typeSolver Symbol solver to resolve type usage.
	 * @return Symbol reference of the resolved value.
	 */
	SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver);
}
