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
package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.SwitchEntry;
import java.util.Optional;

/**
 * The common interface of {@link com.github.javaparser.ast.expr.SwitchExpr} and {@link com.github.javaparser.ast.stmt.SwitchStmt}
 */
public interface SwitchNode {

    NodeList<SwitchEntry> getEntries();

    SwitchEntry getEntry(int i);

    Expression getSelector();

    SwitchNode setEntries(NodeList<SwitchEntry> entries);

    SwitchNode setSelector(Expression selector);

    boolean remove(Node node);

    SwitchNode clone();

    boolean replace(Node node, Node replacementNode);

    Optional<Comment> getComment();

    /**
     * @return true if there are no labels or anything contained in this switch.
     */
    default boolean isEmpty() {
        return getEntries().isEmpty();
    }
    // Too bad Node isn't an interface, or this could have easily inherited all of its methods.
    // Add more when required.
}
