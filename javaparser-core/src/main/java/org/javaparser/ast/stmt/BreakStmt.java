/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
package org.javaparser.ast.stmt;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.expr.SimpleName;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.BreakStmtMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import org.javaparser.metamodel.OptionalProperty;
import java.util.function.Consumer;
import org.javaparser.ast.Generated;

/**
 * <h1>The break statement</h1>
 * <h2>Java 1.0-11</h2>
 * Break has an optional label:
 * <br/><code>break;</code>
 * <br/><code>break somewhere;</code>
 * <br/>The label is in the "value" property as a NameExpr.
 * <h2>Java 12</h2>
 * Break can now also have any expression,
 * to be used in the switch-expression:
 * <br/><code>break 123+456;</code>
 * <br/><code>break "more or less";</code>
 * <br/>The expression will be in the "value" property.
 * <h2>Java 13</h2>
 * The break statement has been reverted to what it was before Java 12, and break-with-value is now the YieldStatement.
 *
 * @author Julio Vilmar Gesser
 * @see org.javaparser.ast.expr.SwitchExpr
 * @see YieldStmt
 */
public class BreakStmt extends Statement {

    @OptionalProperty
    private SimpleName label;

    public BreakStmt() {
        this(null, new SimpleName());
    }

    public BreakStmt(final String label) {
        this(null, new SimpleName(label));
    }

    @AllFieldsConstructor
    public BreakStmt(final SimpleName label) {
        this(null, label);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public BreakStmt(TokenRange tokenRange, SimpleName label) {
        super(tokenRange);
        setLabel(label);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<SimpleName> getLabel() {
        return Optional.ofNullable(label);
    }

    /**
     * Sets the label
     *
     * @param label the label, can be null
     * @return this, the BreakStmt
     */
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public BreakStmt setLabel(final SimpleName label) {
        if (label == this.label) {
            return (BreakStmt) this;
        }
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (label != null) {
            if (node == label) {
                removeLabel();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public BreakStmt removeLabel() {
        return setLabel((SimpleName) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public BreakStmt clone() {
        return (BreakStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public BreakStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.breakStmtMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (label != null) {
            if (node == label) {
                setLabel((SimpleName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBreakStmt() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public BreakStmt asBreakStmt() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBreakStmt(Consumer<BreakStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BreakStmt> toBreakStmt() {
        return Optional.of(this);
    }
}
