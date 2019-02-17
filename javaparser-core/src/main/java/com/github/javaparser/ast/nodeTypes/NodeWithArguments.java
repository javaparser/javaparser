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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;

import static com.github.javaparser.StaticJavaParser.parseExpression;

/**
 * A node with arguments.
 */
public interface NodeWithArguments<N extends Node> {
    N setArguments(NodeList<Expression> arguments);

    NodeList<Expression> getArguments();

    default Expression getArgument(int i) {
        return getArguments().get(i);
    }

    @SuppressWarnings("unchecked")
    default N addArgument(String arg) {
        return addArgument(parseExpression(arg));
    }

    @SuppressWarnings("unchecked")
    default N addArgument(Expression arg) {
        getArguments().add(arg);
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N setArgument(int i, Expression arg) {
        getArguments().set(i, arg);
        return (N) this;
    }

}
