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
package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import static com.github.javaparser.ast.Modifier.Keyword.FINAL;

/**
 * A node that can be final.
 */
public interface NodeWithFinalModifier<N extends Node> extends NodeWithModifiers<N> {

    /**
     * @return true, if the modifier {@code final} is explicitly added to this node. If the node is implicitly final
     * without an explicit modifier (e.g. records, and components of a record), this method should be overridden.
     */
    default boolean isFinal() {
        return hasModifier(FINAL);
    }

    default N setFinal(boolean set) {
        return setModifier(FINAL, set);
    }
}
