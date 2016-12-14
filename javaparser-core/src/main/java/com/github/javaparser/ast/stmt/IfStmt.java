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

package com.github.javaparser.ast.stmt;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class IfStmt extends Statement {

    private Expression condition;

    private Statement thenStmt;

    private Statement elseStmt;

    public IfStmt() {
        this(null,
                new BooleanLiteralExpr(),
                new EmptyStmt(),
                null);
    }

    public IfStmt(final Expression condition, final Statement thenStmt, final Statement elseStmt) {
        this(null, condition, thenStmt, elseStmt);
    }

    public IfStmt(Range range,
                  final Expression condition, final Statement thenStmt, final Statement elseStmt) {
        super(range);
        setCondition(condition);
        setThenStmt(thenStmt);
        setElseStmt(elseStmt);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Expression getCondition() {
        return condition;
    }

    public Optional<Statement> getElseStmt() {
        return Optional.ofNullable(elseStmt);
    }

    public Statement getThenStmt() {
        return thenStmt;
    }

    public IfStmt setCondition(final Expression condition) {
        notifyPropertyChange(ObservableProperty.CONDITION, this.condition, condition);
        this.condition = assertNotNull(condition);
        setAsParentNodeOf(this.condition);
        return this;
    }

    /**
     * Sets the elseStmt
     *
     * @param elseStmt the elseStmt, can be null
     * @return this, the IfStmt
     */
    public IfStmt setElseStmt(final Statement elseStmt) {
        notifyPropertyChange(ObservableProperty.ELSE_STMT, this.elseStmt, elseStmt);
        this.elseStmt = elseStmt;
        setAsParentNodeOf(this.elseStmt);
        return this;
    }

    public IfStmt setThenStmt(final Statement thenStmt) {
        notifyPropertyChange(ObservableProperty.THEN_STMT, this.thenStmt, thenStmt);
        this.thenStmt = assertNotNull(thenStmt);
        setAsParentNodeOf(this.thenStmt);
        return this;
    }
}
