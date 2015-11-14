package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.util.List;

/**
 * Declaration of a Class (not an interface or an enum).
 *
 * @author Federico Tomassetti
 */
public interface ClassDeclaration extends TypeDeclaration, TypeParametrized {

    /**
     * This method should always return true.
     */
    @Override
    default boolean isClass() {
        return true;
    }

    /**
     * This is a ReferenceTypeUsage because it could contain type parameters.
     * For example: class A extends B<Integer, String>.
     * <p/>
     * Note that only the Object class should not have a superclass and therefore
     * return null.
     */
    ReferenceTypeUsage getSuperClass();

    /**
     * Return all the interfaces implemented directly by this class.
     * It does not include the interfaces implemented by superclasses or extended
     * by the interfaces implemented.
     */
    List<InterfaceDeclaration> getInterfaces();

    /**
     * Get all superclasses, with all the type parameters expressed as functions of the type parameters of this
     * declaration.
     */
    List<ReferenceTypeUsage> getAllSuperClasses();

    /**
     * Get all interfaces, with all the type parameters expressed as functions of the type parameters of this
     * declaration.
     */
    List<InterfaceDeclaration> getAllInterfaces();

}
