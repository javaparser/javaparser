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

/**
 * Declaration of a field.
 *
 * @author Federico Tomassetti
 */
public interface ResolvedFieldDeclaration extends ResolvedValueDeclaration, HasAccessSpecifier, HasModifier, HasAnnotations {

    /**
     * Is the field static?
     */
    boolean isStatic();

    /**
     * Is the field volatile?
     */
    boolean isVolatile();

    @Override
    default boolean isField() {
        return true;
    }

    @Override
    default ResolvedFieldDeclaration asField() {
        return this;
    }

    /**
     * The type on which this field has been declared
     */
    ResolvedTypeDeclaration declaringType();

    /**
     * Returns the value of this field if it is a constant field.
     * This method works only if the field type is a primitive type
     * or <code>String</code> type.  Otherwise, it returns <code>null</code>.
     * A constant field is <code>static</code> and <code>final</code>.
     *
     * @return  a <code>Integer</code>, <code>Long</code>, <code>Float</code>,
     *          <code>Double</code>, <code>Boolean</code>,
     *          or <code>String</code> object
     *          representing the constant value.
     *          <code>null</code> if it is not a constant field
     *          or if the field type is not a primitive type
     *          or <code>String</code>.
     */
    Object constantValue();
}
