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
package com.github.javaparser.ast.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.BreakStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * <h1>The break statement</h1>
 * <h2>Java 1.0-11</h2>
 * Break has an optional label:
 * <br>{@code break;}
 * <br>{@code break somewhere;}
 * <br>The label is in the "value" property as a NameExpr.
 * <h2>Java 12</h2>
 * Break can now also have any expression,
 * to be used in the switch-expression:
 * <br>{@code break 123+456;}
 * <br>{@code break "more or less";}
 * <br>The expression will be in the "value" property.
 * <h2>Java 13</h2>
 * The break statement has been reverted to what it was before Java 12, and break-with-value is now the YieldStatement.
 *
 * @author Julio Vilmar Gesser
 * @see com.github.javaparser.ast.expr.SwitchExpr
 * @see YieldStmt
 */
public class BreakStmt extends Statement {

    @OptionalProperty
    private SimpleName label;

    public BreakStmt() {
        this(null, null);
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
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public BreakStmt(TokenRange tokenRange, SimpleName label) {
        super(tokenRange);
        setLabel(label);
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
    public Optional<SimpleName> getLabel() {
        return Optional.ofNullable(label);
    }

    /**
     * Sets the label
     *
     * @param label the label, can be null
     * @return this, the BreakStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BreakStmt setLabel(final SimpleName label) {
        if (label == this.label) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (label != null) {
            if (node == label) {
                removeLabel();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public BreakStmt removeLabel() {
        return setLabel((SimpleName) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public BreakStmt clone() {
        return (BreakStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public BreakStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.breakStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (label != null) {
            if (node == label) {
                setLabel((SimpleName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBreakStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BreakStmt asBreakStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBreakStmt(Consumer<BreakStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BreakStmt> toBreakStmt() {
        return Optional.of(this);
    }
}
