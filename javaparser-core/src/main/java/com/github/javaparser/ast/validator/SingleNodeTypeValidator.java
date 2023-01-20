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
package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

/**
 * Runs a validator on all nodes of a certain type.
 */
public class SingleNodeTypeValidator<N extends Node> implements Validator {

    private final Class<N> type;

    private final TypedValidator<N> validator;

    public SingleNodeTypeValidator(Class<N> type, TypedValidator<N> validator) {
        this.type = type;
        this.validator = validator;
    }

    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
        if (type.isInstance(node)) {
            validator.accept(type.cast(node), problemReporter);
        }
        node.findAll(type).forEach(n -> validator.accept(n, problemReporter));
    }
}
