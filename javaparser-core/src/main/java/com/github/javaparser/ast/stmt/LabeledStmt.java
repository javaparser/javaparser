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
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LabeledStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;

/**
 * A statement that is labeled, like <code>label123: println("continuing");</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class LabeledStmt extends Statement {

    private SimpleName label;

    private Statement statement;

    public LabeledStmt() {
        this(null, new SimpleName(), new ReturnStmt());
    }

    public LabeledStmt(final String label, final Statement statement) {
        this(null, new SimpleName(label), statement);
    }

    @AllFieldsConstructor
    public LabeledStmt(final SimpleName label, final Statement statement) {
        this(null, label, statement);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LabeledStmt(Range range, SimpleName label, Statement statement) {
        super(range);
        setLabel(label);
        setStatement(statement);
        customInitialization();
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Statement getStatement() {
        return statement;
    }

    public LabeledStmt setStatement(final Statement statement) {
        assertNotNull(statement);
        if (statement == this.statement) {
            return (LabeledStmt) this;
        }
        notifyPropertyChange(ObservableProperty.STATEMENT, this.statement, statement);
        if (this.statement != null)
            this.statement.setParentNode(null);
        this.statement = statement;
        setAsParentNodeOf(statement);
        return this;
    }

    public final SimpleName getLabel() {
        return label;
    }

    public LabeledStmt setLabel(final SimpleName label) {
        assertNotNull(label);
        if (label == this.label) {
            return (LabeledStmt) this;
        }
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LabeledStmt clone() {
        return (LabeledStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public LabeledStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.labeledStmtMetaModel;
    }
}
