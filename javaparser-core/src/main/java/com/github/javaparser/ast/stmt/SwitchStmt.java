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
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.SwitchStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * A switch statement.
 * <br/>In <code>switch(a) { ... }</code> the selector is "a",
 * and the contents of the { ... } are the entries.
 *
 * @author Julio Vilmar Gesser
 * @see SwitchEntryStmt
 */
public final class SwitchStmt extends Statement {

    private Expression selector;

    private NodeList<SwitchEntryStmt> entries;

    public SwitchStmt() {
        this(null, new NameExpr(), new NodeList<>());
    }

    @AllFieldsConstructor
    public SwitchStmt(final Expression selector, final NodeList<SwitchEntryStmt> entries) {
        this(null, selector, entries);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SwitchStmt(TokenRange tokenRange, Expression selector, NodeList<SwitchEntryStmt> entries) {
        super(tokenRange);
        setSelector(selector);
        setEntries(entries);
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
    public NodeList<SwitchEntryStmt> getEntries() {
        return entries;
    }

    public SwitchEntryStmt getEntry(int i) {
        return getEntries().get(i);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getSelector() {
        return selector;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchStmt setEntries(final NodeList<SwitchEntryStmt> entries) {
        assertNotNull(entries);
        if (entries == this.entries) {
            return (SwitchStmt) this;
        }
        notifyPropertyChange(ObservableProperty.ENTRIES, this.entries, entries);
        if (this.entries != null)
            this.entries.setParentNode(null);
        this.entries = entries;
        setAsParentNodeOf(entries);
        return this;
    }

    /**
     * @deprecated use a method on getEntries instead
     */
    @Deprecated
    public SwitchStmt setEntry(int i, SwitchEntryStmt entry) {
        getEntries().set(i, entry);
        return this;
    }

    /**
     * @deprecated use a method on getEntries instead
     */
    @Deprecated
    public SwitchStmt addEntry(SwitchEntryStmt entry) {
        getEntries().add(entry);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchStmt setSelector(final Expression selector) {
        assertNotNull(selector);
        if (selector == this.selector) {
            return (SwitchStmt) this;
        }
        notifyPropertyChange(ObservableProperty.SELECTOR, this.selector, selector);
        if (this.selector != null)
            this.selector.setParentNode(null);
        this.selector = selector;
        setAsParentNodeOf(selector);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < entries.size(); i++) {
            if (entries.get(i) == node) {
                entries.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public SwitchStmt clone() {
        return (SwitchStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public SwitchStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.switchStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < entries.size(); i++) {
            if (entries.get(i) == node) {
                entries.set(i, (SwitchEntryStmt) replacementNode);
                return true;
            }
        }
        if (node == selector) {
            setSelector((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchStmt asSwitchStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchStmt(Consumer<SwitchStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SwitchStmt> toSwitchStmt() {
        return Optional.of(this);
    }
}
