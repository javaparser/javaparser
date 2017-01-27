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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A classic for statement.
 * <br/>In <code>for(int a=3,b==5; a<99; a++) { ... }</code> the intialization is int a=3,b=5, 
 * compare is b==5, update is a++, and the statement or block statement following it is in body.  
 *
 * @author Julio Vilmar Gesser
 */
public final class ForStmt extends Statement implements NodeWithBody<ForStmt> {

    private NodeList<Expression> initialization;

    private Expression compare;

    private NodeList<Expression> update;

    private Statement body;

    public ForStmt() {
        this(null,
                new NodeList<>(),
                new BooleanLiteralExpr(),
                new NodeList<>(),
                new ReturnStmt());
    }

    @AllFieldsConstructor
    public ForStmt(final NodeList<Expression> initialization, final Expression compare,
                   final NodeList<Expression> update, final Statement body) {
        this(null, initialization, compare, update, body);
    }

    public ForStmt(Range range,
                   final NodeList<Expression> initialization, final Expression compare,
                   final NodeList<Expression> update, final Statement body) {
        super(range);
        setCompare(compare);
        setInitialization(initialization);
        setUpdate(update);
        setBody(body);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public Statement getBody() {
        return body;
    }

    public Optional<Expression> getCompare() {
        return Optional.ofNullable(compare);
    }

    public NodeList<Expression> getInitialization() {
        return initialization;
    }

    public NodeList<Expression> getUpdate() {
        return update;
    }

    @Override
    public ForStmt setBody(final Statement body) {
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        this.body = body;
        setAsParentNodeOf(this.body);
        return this;
    }

    /**
     * Sets the compare
     *
     * @param compare the compare, can be null
     * @return this, the ForStmt
     */
    public ForStmt setCompare(final Expression compare) {
        notifyPropertyChange(ObservableProperty.COMPARE, this.compare, compare);
        this.compare = compare;
        setAsParentNodeOf(this.compare);
        return this;
    }

    public ForStmt setInitialization(final NodeList<Expression> initialization) {
        notifyPropertyChange(ObservableProperty.INITIALIZER, this.initialization, initialization);
        this.initialization = assertNotNull(initialization);
        setAsParentNodeOf(this.initialization);
        return this;
    }

    public ForStmt setUpdate(final NodeList<Expression> update) {
        notifyPropertyChange(ObservableProperty.UPDATE, this.update, update);
        this.update = assertNotNull(update);
        setAsParentNodeOf(this.update);
        return this;
    }
}
