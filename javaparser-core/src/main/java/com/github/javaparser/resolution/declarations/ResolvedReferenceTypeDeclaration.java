/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.resolution.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public interface ResolvedReferenceTypeDeclaration extends ResolvedTypeDeclaration,
        ResolvedTypeParametrizable {

    @Override
    default ResolvedReferenceTypeDeclaration asReferenceType() {
        return this;
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
    List<ResolvedReferenceType> getAncestors();

    /**
     * The list of all the ancestors of the current declaration, direct and indirect.
     * This list does not contains duplicates with the exacting same type parameters.
     */
    default List<ResolvedReferenceType> getAllAncestors() {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();
        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (!(Object.class.getCanonicalName().equals(getQualifiedName()))) {       
            for (ResolvedReferenceType ancestor : getAncestors()) {
                ancestors.add(ancestor);    
                for (ResolvedReferenceType inheritedAncestor : ancestor.getAllAncestors()) {
                    if (!ancestors.contains(inheritedAncestor)) {
                        ancestors.add(inheritedAncestor);
                    }
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
    default ResolvedFieldDeclaration getField(String name) {
        Optional<ResolvedFieldDeclaration> field = this.getAllFields().stream().filter(f -> f.getName().equals(name)).findFirst();
        if (field.isPresent()) {
            return field.get();
        } else {
            throw new UnsolvedSymbolException("Field not found: " + name);
        }
    }

    /**
     * Consider only field or inherited field which is not private.
     */
    default ResolvedFieldDeclaration getVisibleField(String name) {
        Optional<ResolvedFieldDeclaration> field = getVisibleFields().stream().filter(f -> f.getName().equals(name)).findFirst();
        if (field.isPresent()) {
            return field.get();
        } else {
            throw new IllegalArgumentException();
        }
    }

    /**
     * Has this type a field with the given name?
     */
    default boolean hasField(String name) {
        return this.getAllFields().stream().filter(f -> f.getName().equals(name)).findFirst().isPresent();
    }

    /**
     * Either a declared field or inherited field which is not private.
     */
    default boolean hasVisibleField(String name) {
        return getVisibleFields().stream().filter(f -> f.getName().equals(name)).findFirst().isPresent();
    }

    /**
     * Return a list of all fields, either declared in this declaration or inherited.
     */
    List<ResolvedFieldDeclaration> getAllFields();

    /**
     * Return a list of all fields declared and the inherited ones which are not private.
     */
    default List<ResolvedFieldDeclaration> getVisibleFields() {
        return getAllFields().stream()
                .filter(f -> f.declaringType().equals(this) || f.accessSpecifier() != AccessSpecifier.PRIVATE)
                .collect(Collectors.toList());
    }

    /**
     * Return a list of all the non static fields, either declared or inherited.
     */
    default List<ResolvedFieldDeclaration> getAllNonStaticFields() {
        return getAllFields().stream().filter(it -> !it.isStatic()).collect(Collectors.toList());
    }

    /**
     * Return a list of all the static fields, either declared or inherited.
     */
    default List<ResolvedFieldDeclaration> getAllStaticFields() {
        return getAllFields().stream().filter(it -> it.isStatic()).collect(Collectors.toList());
    }

    /**
     * Return a list of all the fields declared in this type.
     */
    default List<ResolvedFieldDeclaration> getDeclaredFields() {
        return getAllFields().stream().filter(it -> it.declaringType().getQualifiedName().equals(getQualifiedName())).collect(Collectors.toList());
    }

    ///
    /// Methods
    ///

    /**
     * Return a list of all the methods declared in this type declaration.
     */
    Set<ResolvedMethodDeclaration> getDeclaredMethods();

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
    boolean isAssignableBy(ResolvedType type);

    /**
     * Can we assign instances of the type defined by this declaration to variables having the type defined
     * by the given type?
     */
    default boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        return other.isAssignableBy(this);
    }

    /**
     * Can we assign instances of the given type to variables having the type defined
     * by this declaration?
     */
    boolean isAssignableBy(ResolvedReferenceTypeDeclaration other);

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

    ///
    /// Type parameters
    ///

    @Override
    default Optional<ResolvedTypeParameterDeclaration> findTypeParameter(String name) {
        for (ResolvedTypeParameterDeclaration tp : this.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(tp);
            }
        }
        if (this.containerType().isPresent()) {
            return this.containerType().get().findTypeParameter(name);
        }
        return Optional.empty();
    }
}
