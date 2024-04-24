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
package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.AllFieldsConstructor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.PatternExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;

public abstract class PatternExpr extends Expression {

    @AllFieldsConstructor
    public PatternExpr() {
    }

    @Override
    public boolean isPatternExpr() {
        return true;
    }

    @Override
    public PatternExpr asPatternExpr() {
        return this;
    }

    @Override
    public Optional<PatternExpr> toPatternExpr() {
        return Optional.of(this);
    }

    public void ifPatternExpr(Consumer<PatternExpr> action) {
        action.accept(this);
    }

    @Override
    public PatternExpr clone() {
        return (PatternExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public PatternExprMetaModel getMetaModel() {
        return JavaParserMetaModel.patternExprMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public PatternExpr(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }
}
