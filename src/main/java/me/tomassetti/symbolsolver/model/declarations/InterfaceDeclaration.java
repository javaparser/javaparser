package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeSolver;

import java.util.ArrayList;

import java.util.List;

/**
 * An interface declaration.
 */
public interface InterfaceDeclaration extends TypeDeclaration, TypeParametrized {

    @Override
    default boolean isInterface() {
        return true;
    }

    List<InterfaceDeclaration> getInterfacesExtended(TypeSolver typeSolver);

    default List<InterfaceDeclaration> getAllInterfacesExtended(TypeSolver typeSolver) {
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        for (InterfaceDeclaration interfaceDeclaration : getInterfacesExtended(typeSolver)) {
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended(typeSolver));
        }
        return interfaces;
    }
}
