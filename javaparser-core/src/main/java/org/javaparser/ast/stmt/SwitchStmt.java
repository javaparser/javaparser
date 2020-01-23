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
import org.javaparser.ast.NodeList;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.NameExpr;
import org.javaparser.ast.nodeTypes.SwitchNode;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.SwitchStmtMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

/**
 * <h1>The switch statement</h1>
 *
 * <h2>Java 1.0-1.4</h2>
 * The basic C-like switch statement.
 * It can switch only on integers.
 * <br/><code>switch(x) { case 5: case 6: a=100; break; case 9: a=33; break; default: throw new IllegalStateException(); };</code>
 * <br/>In <code>switch(a) { ... }</code> the selector is "a",
 * and the contents of the { ... } are the entries.
 *
 * <h2>Java 5-6</h2>
 * Switching can now also be done on enum constants.
 *
 * <h2>Java 7-11</h2>
 * Switching can now also be done on strings.
 *
 * <h2>Java 12</h2>
 * In preparation for pattern matching, lots of changes are made:
 * <ul>
 * <li>multiple labels per case
 * <li>a -> syntax that does not fall through.
 * <li>break can take any expression (usable in the {@link org.javaparser.ast.expr.SwitchExpr})
 * <li>switch can be used as an expression (it becomes a {@link org.javaparser.ast.expr.SwitchExpr})
 * </ul>
 * <code>switch(x) { case BANANA,PEAR: b=10; break; default: b=5; };</code>
 * <br/><code>switch(x) { case 5,6 -> println("uhuh"); default -> println("nope"); };</code>
 *
 * <h2>Java 13</h2>
 * The break statement has been reverted to what it was before Java 12, and break-with-value is now the YieldStatement.
 *
 * @author Julio Vilmar Gesser
 * @see SwitchEntry
 * @see org.javaparser.ast.expr.SwitchExpr
 * @see SwitchNode
 * @see BreakStmt
 * @see YieldStmt
 */
public class SwitchStmt extends Statement implements SwitchNode {

    private Expression selector;

    private NodeList<SwitchEntry> entries;

    public SwitchStmt() {
        this(null, new NameExpr(), new NodeList<>());
    }

    @AllFieldsConstructor
    public SwitchStmt(final Expression selector, final NodeList<SwitchEntry> entries) {
        this(null, selector, entries);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public SwitchStmt(TokenRange tokenRange, Expression selector, NodeList<SwitchEntry> entries) {
        super(tokenRange);
        setSelector(selector);
        setEntries(entries);
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
    public NodeList<SwitchEntry> getEntries() {
        return entries;
    }

    public SwitchEntry getEntry(int i) {
        return getEntries().get(i);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Expression getSelector() {
        return selector;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public SwitchStmt setEntries(final NodeList<SwitchEntry> entries) {
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

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
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
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public SwitchStmt clone() {
        return (SwitchStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public SwitchStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.switchStmtMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < entries.size(); i++) {
            if (entries.get(i) == node) {
                entries.set(i, (SwitchEntry) replacementNode);
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
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchStmt() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchStmt asSwitchStmt() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchStmt(Consumer<SwitchStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SwitchStmt> toSwitchStmt() {
        return Optional.of(this);
    }
}
