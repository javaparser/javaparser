/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.model.declarations;

import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

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

    /**
     * Get the list of types defined inside the current type.
     */
    default Set<TypeDeclaration> internalTypes() {
        throw new UnsupportedOperationException();
    }

    /**
     * Get the TypeDeclaration enclosing this declaration.
     * @return
     */
    default Optional<TypeDeclaration> containerType() {
        throw new UnsupportedOperationException("containerType is not supported for " + this.getClass().getCanonicalName());
    }

    ///
    /// Misc
    ///

    /**
     * Is this the declaration of a class?
     * Note that an Enum is not considered a Class in this case.
     */
    default boolean isClass() {
        return false;
    }

    /**
     * Is this the declaration of an interface?
     */
    default boolean isInterface() {
        return false;
    }

    /**
     * Is this the declaration of an enum?
     */
    default boolean isEnum() {
        return false;
    }

    /**
     * Is this the declaration of a type parameter?
     */
    default boolean isTypeParameter() {
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

    /**
     * Return this as a ClassDeclaration or throw UnsupportedOperationException.
     */
    default ClassDeclaration asClass() {
        throw new UnsupportedOperationException(String.format("%s is not a class", this));
    }

    /**
     * Return this as a InterfaceDeclaration or throw UnsupportedOperationException.
     */
    default InterfaceDeclaration asInterface() {
        throw new UnsupportedOperationException(String.format("%s is not an interface", this));
    }

    /**
     * Return this as a EnumDeclaration or throw UnsupportedOperationException.
     */
    default EnumDeclaration asEnum() {
        throw new UnsupportedOperationException(String.format("%s is not an enum", this));
    }

    /**
     * Return this as a TypeParameterDeclaration or throw UnsupportedOperationException.
     */
    default TypeParameterDeclaration asTypeParameter() {
        throw new UnsupportedOperationException(String.format("%s is not a type parameter", this));
    }

    /**
     * The fully qualified name of the type declared.
     */
    String getQualifiedName();

    /**
     * The ID corresponds most of the type to the qualified name. It differs only for local
     * classes which do not have a qualified name but have an ID.
     */
    default String getId() {
        String qname = getQualifiedName();
        if (qname == null) {
            return String.format("<localClass>:%s", getName());
        }
        return qname;
    }

    ///
    /// Type parameters
    ///

    @Override
    default Optional<TypeParameterDeclaration> findTypeParameter(String name) {
        for (TypeParameterDeclaration tp : this.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(tp);
            }
        }
        if (this.containerType().isPresent()) {
            return this.containerType().get().findTypeParameter(name);
        }
        return Optional.empty();
    }

    ///
    /// Ancestors
    ///

    /**
     * The list of all the direct ancestors of the current declaration.
     * Note that the ancestor can be parametrized types with values specified. For example:
     * <p>
     * class A implements Comparable&lt;String&gt; {}
     * <p>
     * In this case the ancestor is Comparable&lt;String&gt;
     */
    List<ReferenceType> getAncestors();

    /**
     * The list of all the ancestors of the current declaration, direct and indirect.
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
     * <p>
     * class Foo<E> { E field; }
     * <p>
     * class Bar extends Foo<String> { }
     * <p>
     * When calling getField("field") on Foo I should get a FieldDeclaration with type E, while calling it on
     * Bar I should get a FieldDeclaration with type String.
     */
    FieldDeclaration getField(String name);

    /**
     * Has this type a field with the given name?
     */
    boolean hasField(String name);

    /**
     * Return a list of all fields, either declared in this declaration or inherited.
     */
    List<FieldDeclaration> getAllFields();

    /**
     * Return a list of all the non static fields, either declared or inherited.
     */
    default List<FieldDeclaration> getAllNonStaticFields() {
        return getAllFields().stream().filter(it -> !it.isStatic()).collect(Collectors.toList());
    }

    /**
     * Return a list of all the static fields, either declared or inherited.
     */
    default List<FieldDeclaration> getAllStaticFields() {
        return getAllFields().stream().filter(it -> it.isStatic()).collect(Collectors.toList());
    }

    /**
     * Return a list of all the fields declared in this type.
     */
    default List<FieldDeclaration> getDeclaredFields() {
        return getAllFields().stream().filter(it -> it.declaringType().getQualifiedName().equals(getQualifiedName())).collect(Collectors.toList());
    }

    ///
    /// Methods
    ///

    /**
     * Return a list of all the methods declared in this type declaration.
     */
    Set<MethodDeclaration> getDeclaredMethods();

    /**
     * Return a list of all the methods declared of this type declaration, either declared or inherited.
     * Note that it should not include overridden methods.
     */
    Set<MethodUsage> getAllMethods();

    ///
    /// Assignability
    ///

    /**
     * Can we assign instances of the given type to variables having the type defined
     * by this declaration?
     */
    boolean isAssignableBy(Type type);

    /**
     * Can we assign instances of the type defined by this declaration to variables having the type defined
     * by the given type?
     */
    default boolean canBeAssignedTo(TypeDeclaration other) {
        return other.isAssignableBy(this);
    }

    /**
     * Can we assign instances of the given type to variables having the type defined
     * by this declaration?
     */
    boolean isAssignableBy(TypeDeclaration other);

    ///
    /// Annotations
    ///

    /**
     * Has the type at least one annotation declared having the specified qualified name?
     */
    boolean hasDirectlyAnnotation(String qualifiedName);

    /**
     * Has the type at least one annotation declared or inherited having the specified qualified name?
     */
    default boolean hasAnnotation(String qualifiedName) {
        if (hasDirectlyAnnotation(qualifiedName)) {
            return true;
        }
        return getAllAncestors().stream().anyMatch(it -> it.asReferenceType().getTypeDeclaration().hasDirectlyAnnotation(qualifiedName));
    }

    /**
     * This means that the type has a functional method. Conceptually, a functional interface has exactly one abstract method.
     * Typically these classes has the FunctionInterface annotation but this is not mandatory.
     */
    boolean isFunctionalInterface();

}
