package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.resolution.TypeSolver;

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

    List<InterfaceDeclaration> getInterfacesExtended();

    default List<InterfaceDeclaration> getAllInterfacesExtended() {
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        for (InterfaceDeclaration interfaceDeclaration : getInterfacesExtended()) {
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended());
        }
        return interfaces;
    }
}
