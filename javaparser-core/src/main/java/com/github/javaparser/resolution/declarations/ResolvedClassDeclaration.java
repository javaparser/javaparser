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

import com.github.javaparser.resolution.types.ResolvedReferenceType;

import java.util.List;

/**
 * Declaration of a Class (not an interface or an enum).
 *
 * @author Federico Tomassetti
 */
public interface ResolvedClassDeclaration extends ResolvedReferenceTypeDeclaration,
        ResolvedTypeParametrizable, HasAccessSpecifier {

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
     * <p>
     * Note that only the Object class should not have a superclass and therefore
     * return null.
     */
    ResolvedReferenceType getSuperClass();

    /**
     * Return all the interfaces implemented directly by this class.
     * It does not include the interfaces implemented by superclasses or extended
     * by the interfaces implemented.
     */
    List<ResolvedReferenceType> getInterfaces();

    /**
     * Get all superclasses, with all the type typeParametersValues expressed as functions of the type
     * typeParametersValues of this declaration.
     */
    List<ResolvedReferenceType> getAllSuperClasses();

    /**
     * Return all the interfaces implemented by this class, either directly or indirectly, including the interfaces
     * extended by interfaces it implements.
     * <p>
     * Get all interfaces, with all the type typeParametersValues expressed as functions of the type
     * typeParametersValues of this declaration.
     */
    List<ResolvedReferenceType> getAllInterfaces();

    ///
    /// Constructors
    ///

    /**
     * List of constructors available for the class.
     * This list should also include the default constructor.
     */
    List<ResolvedConstructorDeclaration> getConstructors();

}
