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

import com.github.javaparser.resolution.types.ResolvedType;

/**
 * A declaration of a method (either in an interface, a class, an enum or an annotation).
 *
 * @author Federico Tomassetti
 */
public interface ResolvedMethodDeclaration extends ResolvedMethodLikeDeclaration {

    /**
     * The type of the value returned by the current method. This method can also be invoked
     * for methods returning void.
     */
    ResolvedType getReturnType();

    /**
     * Is the method abstract? All interface methods not marked as default are abstract.
     */
    boolean isAbstract();

    /**
     * Is this a default method?
     */
    boolean isDefaultMethod();

    /*
     * Is this method static?
     */
    boolean isStatic();

    /*
     * Returns the method descriptor (https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.3.3)
     * The method descriptor for the method: {@code Object m(int i, double d, Thread t) {...}}
     * is {@code (IDLjava/lang/Thread;)Ljava/lang/Object;}
     * Note that the internal forms of the binary names of Thread and Object are used.
     */
    String toDescriptor();

    /*
     * A method declaration d1 with return type R1 is return-type-substitutable
     * for another method d2 with return type R2 if any of the following is true:
     * If R1 is void then R2 is void.
     * If R1 is a primitive type then R2 is identical to R1.
     * If R1 is a reference type then one of the following is true:
     * R1, adapted to the type parameters of d2 (§8.4.4), is a subtype of R2.
     * R1 can be converted to a subtype of R2 by unchecked conversion (§5.1.9).
     * d1 does not have the same signature as d2 (§8.4.2), and R1 = |R2|.
     * TODO: Probably this method needs to refer to a method "isTypeSubstituable" implemented in ResolvedType
     */
    default boolean isReturnTypeSubstituable(ResolvedType otherResolvedType) {
        ResolvedType returnType = getReturnType();
        if (returnType.isVoid()) {
            return otherResolvedType.isVoid();
        }
        if (returnType.isPrimitive()) {
            return otherResolvedType.isPrimitive() && returnType.asPrimitive().equals(otherResolvedType.asPrimitive());
        }
        // If R1 is a reference type then one of the following is true:
        // R1, adapted to the type parameters of d2 (§8.4.4), is a subtype of R2.
        // Below we are trying to compare a reference type for example an Object to a type variable let's say T
        // we can certainly simplify by saying that this is always true.
        if (otherResolvedType.isTypeVariable()) {
            return true;
        }
        // R1 can be converted to a subtype of R2 by unchecked conversion (§5.1.9).
        // d1 does not have the same signature as d2 (§8.4.2), and R1 = |R2|.
        if (returnType.describe().equals(otherResolvedType.erasure().describe())) {
            return true;
        }
        throw new UnsupportedOperationException("Return-Type-Substituable must be implemented on reference type.");
    }
}
