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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.Node;

/**
 * We want to recognize do not consider "phantom" nodes, like the fake type of variable in FieldDeclaration
 */
public class PhantomNodeLogic {

    public static boolean isPhantomNode(Node node) {
        return node.getParentNode().isPresent() && !node.getParentNode().get().getRange().get().contains(node.getRange().get()) || inPhantomNode(node, 3);
    }

    /**
     * A node contained in a phantom node is also a phantom node. We limit how many levels up we check just for performance reasons.
     */
    private static boolean inPhantomNode(Node node, int levels) {
        return node.getParentNode().isPresent() && (isPhantomNode(node.getParentNode().get()) || inPhantomNode(node.getParentNode().get(), levels - 1));
    }
}
