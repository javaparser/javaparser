package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

/**
 * @author Federico Tomassetti
 */
public interface ValueDeclaration extends Declaration {

    TypeUsage getType(TypeSolver typeSolver);

}
