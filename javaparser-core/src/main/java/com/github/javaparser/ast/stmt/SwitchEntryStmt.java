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

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.metamodel.SwitchEntryStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;

/**
 * One case in a switch statement.
 * <br/><pre>
 * switch (i) {
 * case 1:
 * case 2:
 * System.out.println(444);
 * break;
 * default:
 * System.out.println(0);
 * }
 * </pre>
 * This contains three SwitchEntryStmts.
 * <br/>The first one has label 1 and no statements.
 * <br/>The second has label 2 and two statements (the println and the break).
 * <br/>The third, the default, has no label and one statement.
 *
 * @author Julio Vilmar Gesser
 * @see SwitchStmt
 */
public final class SwitchEntryStmt extends Statement implements NodeWithStatements<SwitchEntryStmt> {

    @OptionalProperty
    private Expression label;

    private NodeList<Statement> statements;

    public SwitchEntryStmt() {
        this(null, null, new NodeList<>());
    }

    @AllFieldsConstructor
    public SwitchEntryStmt(final Expression label, final NodeList<Statement> statements) {
        this(null, label, statements);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SwitchEntryStmt(TokenRange tokenRange, Expression label, NodeList<Statement> statements) {
        super(tokenRange);
        setLabel(label);
        setStatements(statements);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getLabel() {
        return Optional.ofNullable(label);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Statement> getStatements() {
        return statements;
    }

    /**
     * Sets the label
     *
     * @param label the label, can be null
     * @return this, the SwitchEntryStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntryStmt setLabel(final Expression label) {
        if (label == this.label) {
            return (SwitchEntryStmt) this;
        }
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntryStmt setStatements(final NodeList<Statement> statements) {
        assertNotNull(statements);
        if (statements == this.statements) {
            return (SwitchEntryStmt) this;
        }
        notifyPropertyChange(ObservableProperty.STATEMENTS, this.statements, statements);
        if (this.statements != null)
            this.statements.setParentNode(null);
        this.statements = statements;
        setAsParentNodeOf(statements);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (label != null) {
            if (node == label) {
                removeLabel();
                return true;
            }
        }
        for (int i = 0; i < statements.size(); i++) {
            if (statements.get(i) == node) {
                statements.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public SwitchEntryStmt removeLabel() {
        return setLabel((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public SwitchEntryStmt clone() {
        return (SwitchEntryStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public SwitchEntryStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.switchEntryStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (label != null) {
            if (node == label) {
                setLabel((Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < statements.size(); i++) {
            if (statements.get(i) == node) {
                statements.set(i, (Statement) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchEntryStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchEntryStmt asSwitchEntryStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchEntryStmt(Consumer<SwitchEntryStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SwitchEntryStmt> toSwitchEntryStmt() {
        return Optional.of(this);
    }
}
