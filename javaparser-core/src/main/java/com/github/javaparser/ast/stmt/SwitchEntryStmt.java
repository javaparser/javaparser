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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class SwitchEntryStmt extends Statement implements NodeWithStatements<SwitchEntryStmt> {

    private Expression label;

    private NodeList<Statement> statements;

    public SwitchEntryStmt() {
        this(null, null, new NodeList<>());
    }

    public SwitchEntryStmt(final Expression label, final NodeList<Statement> statements) {
        this(null, label, statements);
    }

    public SwitchEntryStmt(Range range, final Expression label,
                           final NodeList<Statement> statements) {
        super(range);
        setLabel(label);
        setStatements(statements);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Optional<Expression> getLabel() {
        return Optional.ofNullable(label);
    }

    public NodeList<Statement> getStatements() {
        return statements;
    }

    /**
     * Sets the label
     *
     * @param label the label, can be null
     * @return this, the SwitchEntryStmt
     */
    public SwitchEntryStmt setLabel(final Expression label) {
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        this.label = label;
        setAsParentNodeOf(this.label);
        return this;
    }

    public SwitchEntryStmt setStatements(final NodeList<Statement> statements) {
        notifyPropertyChange(ObservableProperty.STATEMENTS, this.statements, statements);
        this.statements = assertNotNull(statements);
        setAsParentNodeOf(this.statements);
        return this;
    }
}
