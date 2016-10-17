package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * A declaration of a type. It could be a primitive type, an enum, a class, an interface or a type variable.
 * It cannot be an annotation or an array.
 *
 * @author Federico Tomassetti
 */
public interface TypeDeclaration extends Declaration, TypeParametrizable {

    ///
    /// Containment
    ///

    default Set<TypeDeclaration> internalTypes() {
        throw new UnsupportedOperationException();
    }

    default Optional<TypeDeclaration> containerType() {
        throw new UnsupportedOperationException();
    }

    ///
    /// Misc
    ///

    default boolean isClass() {
        return false;
    }

    default boolean isInterface() {
        return false;
    }

    default boolean isEnum() {
        return false;
    }

    default boolean isTypeVariable() {
        return false;
    }

    @Override
    default boolean isType() {
        return true;
    }

    @Override
    default TypeDeclaration asType() {
        return this;
    }

    default ClassDeclaration asClass() {
        throw new UnsupportedOperationException(String.format("%s is not a class", this));
    }

    default InterfaceDeclaration asInterface() {
        throw new UnsupportedOperationException(String.format("%s is not an interface", this));
    }

    default EnumDeclaration asEnum() {
        throw new UnsupportedOperationException(String.format("%s is not an enum", this));
    }

    String getQualifiedName();

    ///
    /// Ancestors
    ///

    List<ReferenceType> getAncestors();

    /**
     * This list does not contains duplicates with the exacting same type parameters.
     */
    default List<ReferenceType> getAllAncestors() {
        List<ReferenceType> ancestors = new ArrayList<>();
        for (ReferenceType ancestor : getAncestors()) {
            ancestors.add(ancestor);
            for (ReferenceType inheritedAncestor : ancestor.getAllAncestors()) {
                if (!ancestors.contains(inheritedAncestor)) {
                    ancestors.add(inheritedAncestor);
                }
            }
        }
        return ancestors;
    }

    ///
    /// Fields
    ///

    /**
     * Note that the type of the field should be expressed using the type variables of this particular type.
     * Consider for example:
     *
     * class Foo<E> { E field; }
     *
     * class Bar extends Foo<String> { }
     *
     * When calling getField("field") on Foo I should get a FieldDeclaration with type E, while calling it on
     * Bar I should get a FieldDeclaration with type String.
     */
    FieldDeclaration getField(String name);

    boolean hasField(String name);
    
    List<FieldDeclaration> getAllFields();

    default List<FieldDeclaration> getAllNonStaticFields() {
        return getAllFields().stream().filter(it -> !it.isStatic()).collect(Collectors.toList());
    }

    default List<FieldDeclaration> getAllStaticFields() {
        return getAllFields().stream().filter(it -> it.isStatic()).collect(Collectors.toList());
    }

    default List<FieldDeclaration> getDeclaredFields() {
        return getAllFields().stream().filter(it ->it.declaringType().getQualifiedName().equals(getQualifiedName())).collect(Collectors.toList());
    }

    ///
    /// Methods
    ///

    Set<MethodDeclaration> getDeclaredMethods();

    Set<MethodUsage> getAllMethods();

    ///
    /// Assignability
    ///

    boolean isAssignableBy(Type type);

    default boolean canBeAssignedTo(TypeDeclaration other) {
        return other.isAssignableBy(this);
    }

    boolean isAssignableBy(TypeDeclaration other);

    ///
    /// Annotations
    ///

    boolean hasDirectlyAnnotation(String canonicalName);

    default boolean hasAnnotation(String canonicalName) {
        if (hasDirectlyAnnotation(canonicalName)) {
            return true;
        }
        return getAllAncestors().stream().anyMatch(it -> it.asReferenceType().getTypeDeclaration().hasDirectlyAnnotation(canonicalName));
    }

}
