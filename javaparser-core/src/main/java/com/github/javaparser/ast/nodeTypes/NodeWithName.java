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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;

import static com.github.javaparser.JavaParser.parseName;
import static com.github.javaparser.utils.Utils.assertNonEmpty;

/**
 * A node with a (qualified) name.
 * <p>
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with a getName method.
 *
 * @since 2.0.1
 */
public interface NodeWithName<N extends Node> {
    Name getName();

    N setName(Name name);

    @SuppressWarnings("unchecked")
    default N setName(String name) {
        assertNonEmpty(name);
        return setName(parseName(name));
    }

    default String getNameAsString() {
        return getName().asString();
    }
}
