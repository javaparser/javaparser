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

/**
 * Declaration of a parameter.
 *
 * @author Federico Tomassetti
 */
public interface ResolvedParameterDeclaration extends ResolvedValueDeclaration {

    @Override
    default boolean isParameter() {
        return true;
    }

    @Override
    default ResolvedParameterDeclaration asParameter() {
        return this;
    }

    /**
     * Is this parameter declared as variadic?
     */
    boolean isVariadic();

    /**
     * Describe the type of the parameter. In practice add three dots to the type name
     * is the parameter is variadic.
     */
    default String describeType() {
        if (isVariadic()) {
            return getType().asArrayType().getComponentType().describe() + "...";
        } else {
            return getType().describe();
        }
    }
}
