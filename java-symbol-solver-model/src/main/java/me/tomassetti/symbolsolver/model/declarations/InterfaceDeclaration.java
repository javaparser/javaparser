package me.tomassetti.symbolsolver.model.declarations;

import java.util.ArrayList;
import java.util.List;

/**
 * An interface declaration.
 *
 * @author Federico Tomassetti
 */
public interface InterfaceDeclaration extends TypeDeclaration, TypeParametrizable {

    @Override
    default boolean isInterface() {
        return true;
    }

    /**
     * Return the list of interfaces extended directly by this one.
     */
    List<InterfaceDeclaration> getInterfacesExtended();

    /**
     * Return the list of interfaces extended directly or indirectly by this one.
     */
    default List<InterfaceDeclaration> getAllInterfacesExtended() {
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        for (InterfaceDeclaration interfaceDeclaration : getInterfacesExtended()) {
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended());
        }
        return interfaces;
    }
}
