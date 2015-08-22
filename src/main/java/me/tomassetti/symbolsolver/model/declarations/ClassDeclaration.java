package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeSolver;

/**
 * A class declaration.
 */
public interface ClassDeclaration extends TypeDeclaration, TypeParametrized {

    @Override
    default boolean isClass() {
        return true;
    }

    TypeDeclaration getSuperClass(TypeSolver typeSolvers);

}
