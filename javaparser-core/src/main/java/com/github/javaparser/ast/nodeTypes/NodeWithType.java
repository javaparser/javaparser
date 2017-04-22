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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.Type;

import static com.github.javaparser.JavaParser.parseType;
import static com.github.javaparser.utils.Utils.assertNonEmpty;

/**
 * A node with a type.
 * <p>
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with getType/setType
 * methods
 *
 * @since 2.3.1
 */
public interface NodeWithType<N extends Node, T extends Type> {
    /**
     * Gets the type
     *
     * @return the type
     */
    T getType();

    /**
     * Sets the type
     *
     * @param type the type
     * @return this
     */
    N setType(T type);

    void tryAddImportToParentCompilationUnit(Class<?> clazz);

    /**
     * Sets this type to this class and try to import it to the {@link CompilationUnit} if needed
     *
     * @param typeClass the type
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N setType(Class<?> typeClass) {
        tryAddImportToParentCompilationUnit(typeClass);
        return setType((T) parseType(typeClass.getSimpleName()));
    }

    @SuppressWarnings("unchecked")
    default N setType(final String typeString) {
        assertNonEmpty(typeString);
        return setType((T) parseType(typeString));
    }

}
