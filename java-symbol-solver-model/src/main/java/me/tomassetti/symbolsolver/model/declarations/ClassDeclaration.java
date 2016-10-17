package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;

import java.util.List;

/**
 * Declaration of a Class (not an interface or an enum).
 *
 * @author Federico Tomassetti
 */
public interface ClassDeclaration extends TypeDeclaration, TypeParametrizable, HasAccessLevel {

    /**
     * This method should always return true.
     */
    @Override
    default boolean isClass() {
        return true;
    }

    /**
     * This is a ReferenceTypeUsage because it could contain type typeParametersValues.
     * For example: class A extends B<Integer, String>.
     * <p/>
     * Note that only the Object class should not have a superclass and therefore
     * return null.
     */
    ReferenceType getSuperClass();

    /**
     * Return all the interfaces implemented directly by this class.
     * It does not include the interfaces implemented by superclasses or extended
     * by the interfaces implemented.
     */
    List<ReferenceType> getInterfaces();

    /**
     * Get all superclasses, with all the type typeParametersValues expressed as functions of the type typeParametersValues of this
     * declaration.
     */
    List<ReferenceType> getAllSuperClasses();

    /**
     * Return all the interfaces implemented by this class, either directly or indirectly, including the interfaces
     * extended by interfaces it implements.
     *
     * Get all interfaces, with all the type typeParametersValues expressed as functions of the type typeParametersValues of this
     * declaration.
     */
    List<ReferenceType> getAllInterfaces();


    ///
    /// Constructors
    ///

    List<ConstructorDeclaration> getConstructors();

}
