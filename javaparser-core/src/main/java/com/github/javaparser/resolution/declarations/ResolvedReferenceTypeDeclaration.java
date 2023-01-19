/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public interface ResolvedReferenceTypeDeclaration extends ResolvedTypeDeclaration, ResolvedTypeParametrizable {

    String JAVA_LANG_ENUM = java.lang.Enum.class.getCanonicalName();

    String JAVA_LANG_OBJECT = java.lang.Object.class.getCanonicalName();

    @Override
    default ResolvedReferenceTypeDeclaration asReferenceType() {
        return this;
    }

    @Override
    default boolean isReferenceType() {
        return true;
    }

    // /
    // / Ancestors
    // /
    /**
     * Resolves the types of all direct ancestors (i.e., the directly extended class and the directly implemented
     * interfaces) and returns the list of ancestors as a list of resolved reference types.
     * <p>
     * In case any ancestor cannot be resolved, an {@code UnsolvedSymbolException} is thrown. In order to obtain a list
     * of only the resolvable direct ancestors, use {@link #getAncestors(boolean)} and pass the value {@code true}.
     * <p>
     * Note that an ancestor can be parametrized types with values specified. For example:
     * <p>
     * class A implements Comparable&lt;String&gt; {}
     * <p>
     * In this case the ancestor is Comparable&lt;String&gt;
     *
     * @return The list of resolved ancestors.
     * @throws UnsolvedSymbolException if some ancestor could not be resolved.
     */
    default List<ResolvedReferenceType> getAncestors() {
        return getAncestors(false);
    }

    /**
     * Resolves the types of all direct ancestors (i.e., the directly extended class and the directly implemented
     * interfaces) and returns the list of ancestors as a list of resolved reference types.
     * <p>
     * If {@code acceptIncompleteList} is {@code false}, then an {@code UnsolvedSymbolException} is thrown if any
     * ancestor cannot be resolved. Otherwise, a list of only the resolvable direct ancestors is returned.
     *
     * @param acceptIncompleteList When set to {@code false}, this method throws an {@link UnsolvedSymbolException} if
     *                             one or more ancestor could not be resolved. When set to {@code true}, this method
     *                             does not throw an {@link UnsolvedSymbolException}, but the list of returned ancestors
     *                             may be incomplete in case one or more ancestor could not be resolved.
     * @return The list of resolved ancestors.
     * @throws UnsolvedSymbolException if some ancestor could not be resolved and {@code acceptIncompleteList} is set to
     *                                 {@code false}.
     */
    List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList);

    /**
     * The list of all the ancestors of the current declaration, direct and indirect.
     * This list does not contains duplicates with the exact same type parameters.
     * For example
     * if A inherits from B, and B inherits from C and implements D, and C inherits from E
     * By default the traversal is depth first
     */
    default List<ResolvedReferenceType> getAllAncestors() {
        return getAllAncestors(depthFirstFunc);
    }

    /**
     * The list of all the ancestors of the current declaration, direct and indirect.
     * This list does not contains duplicates with the exact same type parameters.
     * For example
     * if A inherits from B, and B inherits from C and implements D, and C inherits from E
     * Apply the specified traversal
     */
    default List<ResolvedReferenceType> getAllAncestors(Function<ResolvedReferenceTypeDeclaration, List<ResolvedReferenceType>> traverser) {
        return traverser.apply(this);
    }

    /*
     * depth first search all ancestors
     * In the example above, this method returns B,C,E,D
     */
    Function<ResolvedReferenceTypeDeclaration, List<ResolvedReferenceType>> depthFirstFunc = (rrtd) -> {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();
        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (!rrtd.isJavaLangObject()) {
            for (ResolvedReferenceType ancestor : rrtd.getAncestors()) {
                ancestors.add(ancestor);
                for (ResolvedReferenceType inheritedAncestor : ancestor.getAllAncestors()) {
                    if (!ancestors.contains(inheritedAncestor)) {
                        ancestors.add(inheritedAncestor);
                    }
                }
            }
        }
        return ancestors;
    };

    /*
     * breadth first search all ancestors
     * In the example above, this method returns B,C,D,E
     */
    Function<ResolvedReferenceTypeDeclaration, List<ResolvedReferenceType>> breadthFirstFunc = (rrtd) -> {
    	List<ResolvedReferenceType> ancestors = new ArrayList<>();
        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (!rrtd.isJavaLangObject()) {
            // init direct ancestors
            Deque<ResolvedReferenceType> queuedAncestors = new LinkedList<>(rrtd.getAncestors());
            ancestors.addAll(queuedAncestors);
            while (!queuedAncestors.isEmpty()) {
                ResolvedReferenceType queuedAncestor = queuedAncestors.removeFirst();
                queuedAncestor.getTypeDeclaration().ifPresent(rtd -> new LinkedHashSet<>(queuedAncestor.getDirectAncestors()).stream().forEach(ancestor -> {
                    // add this ancestor to the queue (for a deferred search)
                    queuedAncestors.add(ancestor);
                    // add this ancestor to the list of ancestors
                    if (!ancestors.contains(ancestor)) {
                    	ancestors.add(ancestor);
                    }
                }));
            }
        }
        return ancestors;
    };

    // /
    // / Fields
    // /
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
        return this.getAllFields().stream().anyMatch(f -> f.getName().equals(name));
    }

    /**
     * Either a declared field or inherited field which is not private.
     */
    default boolean hasVisibleField(String name) {
        return getVisibleFields().stream().anyMatch(f -> f.getName().equals(name));
    }

    /**
     * Return a list of all fields, either declared in this declaration or inherited.
     */
    List<ResolvedFieldDeclaration> getAllFields();

    /**
     * Return a list of all fields declared and the inherited ones which are not private.
     */
    default List<ResolvedFieldDeclaration> getVisibleFields() {
        return getAllFields().stream().filter(f -> f.declaringType().equals(this) || f.accessSpecifier() != AccessSpecifier.PRIVATE).collect(Collectors.toList());
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

    // /
    // / Methods
    // /
    /**
     * Return a list of all the methods declared in this type declaration.
     */
    Set<ResolvedMethodDeclaration> getDeclaredMethods();

    /**
     * Return a list of all the methods declared of this type declaration, either declared or inherited.
     * Note that it should not include overridden methods.
     */
    Set<MethodUsage> getAllMethods();

    // /
    // / Assignability
    // /
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

    // /
    // / Annotations
    // /
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
        return getAllAncestors().stream().filter(it -> it.asReferenceType().getTypeDeclaration().isPresent()).anyMatch(it -> it.asReferenceType().getTypeDeclaration().get().hasDirectlyAnnotation(qualifiedName));
    }

    /**
     * This means that the type has a functional method. Conceptually, a functional interface has exactly one abstract method.
     * Typically these classes has the FunctionInterface annotation but this is not mandatory.
     */
    boolean isFunctionalInterface();

    // /
    // / Type parameters
    // /
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

    List<ResolvedConstructorDeclaration> getConstructors();

    /**
     * We don't make this _ex_plicit in the data representation because that would affect codegen
     * and make everything generate like {@code <T extends Object>} instead of {@code <T>}
     *
     * @return true, if this represents {@code java.lang.Object}
     * @see ResolvedReferenceType#isJavaLangObject()
     * @see <a href="https://github.com/javaparser/javaparser/issues/2044">https://github.com/javaparser/javaparser/issues/2044</a>
     */
    default boolean isJavaLangObject() {
        return this.isClass() && !isAnonymousClass() && // Consider anonymous classes
        hasName() && getQualifiedName().equals(JAVA_LANG_OBJECT);
    }

    /**
     * @return true, if this represents {@code java.lang.Enum}
     * @see ResolvedReferenceType#isJavaLangEnum()
     */
    default boolean isJavaLangEnum() {
        return this.isEnum() && getQualifiedName().equals(JAVA_LANG_ENUM);
    }
}
