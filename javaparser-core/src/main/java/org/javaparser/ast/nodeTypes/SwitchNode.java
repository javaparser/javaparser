/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package org.javaparser.ast.nodeTypes;

import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.comments.Comment;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.stmt.SwitchEntry;

import java.util.Optional;

/**
 * The common interface of {@link org.javaparser.ast.expr.SwitchExpr} and {@link org.javaparser.ast.stmt.SwitchStmt}
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
