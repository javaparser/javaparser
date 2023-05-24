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

import com.github.javaparser.ast.Node;
import java.util.Optional;

/**
 * A declaration that can be potentially associated with an AST node.
 */
public interface AssociableToAST {

    /**
     * If the declaration is associated to an AST node return it, otherwise it return empty.
     * Declaration based on source code have an AST node associated while others don't. Example
     * of other declarations are declarations coming from reflection or JARs.
     *
     * You may wonder how this method is different from the various getWrappedNode.
     * The difference is that toAst is present in all Resolved* declarations (such as
     * ResolvedAnnotationDeclaration), while getWrappedNode is present
     * only on the subclasses of the Resolved* declarations that derive from JP AST nodes (such as
     * JavaParserClassDeclaration). Therefore one
     * which has a Resolved* declaration need to do a downcast before being able to use getWrappedNode.
     *
     * Now, this means that toAst could potentially replace getWrappedNode (but not the other way around!).
     * However toAst return an Optional, which is less convenient than getting the direct node. Also,
     * toAst sometimes have to return a more generic node. This is the case for subclasses of
     * ResolvedClassDeclaration. In those cases toAst return a Node. Why? Because both anonymous
     * class declarations and standard class declarations are subclasses of that. In one case the
     * underlying AST node is an ObjectCreationExpr, while in the other case it is ClassOrInterfaceDeclaration.
     * In these cases getWrappedNode is particularly nice because it returns the right type of AST node,
     * not just a Node.
     */
    default Optional<Node> toAst() {
        return Optional.empty();
    }

    /**
     * If the declaration is associated to an AST node and the type matches the expected {@link Class} return it,
     * otherwise it returns empty.
     *
     * @param clazz The expected class of the AST Node.
     * @param <N>   The expected type of AST Node.
     *
     * @return The declaration with the expected {@link Class}.
     *
     * @see AssociableToAST#toAst()
     */
    default <N extends Node> Optional<N> toAst(Class<N> clazz) {
        return toAst().filter(clazz::isInstance).map(clazz::cast);
    }
}
