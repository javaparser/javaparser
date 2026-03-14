/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import static com.github.javaparser.utils.Utils.assertNonEmpty;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import java.util.Optional;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A node with a name.
 * <p>
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with a getName method.
 */
@NullMarked
public interface NodeWithOptionalSimpleName<N extends Node> {

    Optional<SimpleName> getName();

    N setName(@Nullable SimpleName name);

    @SuppressWarnings("unchecked")
    default N setName(@Nullable String name) {
        assertNonEmpty(name);
        return setName(new SimpleName(name));
    }

    default Optional<String> getNameAsString() {
        return getName().map(SimpleName::getIdentifier);
    }

    default Optional<NameExpr> getNameAsExpression() {
        return getName().map(NameExpr::new);
    }

    @Nullable
    SimpleName name();

    default @Nullable String nameAsString() {
        return name() != null ? name().getIdentifier() : null;
    }

    default @Nullable NameExpr nameAsExpression() {
        return name() != null ? new NameExpr(name()) : null;
    }
}
