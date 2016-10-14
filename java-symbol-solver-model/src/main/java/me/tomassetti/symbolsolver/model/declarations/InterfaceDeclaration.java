package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;

import java.util.ArrayList;
import java.util.List;

/**
 * An interface declaration.
 *
 * @author Federico Tomassetti
 */
public interface InterfaceDeclaration extends TypeDeclaration, TypeParametrizable, HasAccessLevel {

    @Override
    default boolean isInterface() {
        return true;
    }

    /**
     * Return the list of interfaces extended directly by this one.
     */
    List<ReferenceType> getInterfacesExtended();

    /**
     * Return the list of interfaces extended directly or indirectly by this one.
     */
    default List<ReferenceType> getAllInterfacesExtended() {
        List<ReferenceType> interfaces = new ArrayList<>();
        for (ReferenceType interfaceDeclaration : getInterfacesExtended()) {
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesAncestors());
        }
        return interfaces;
    }
}
