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
package com.github.javaparser.ast.stmt;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.DerivedProperty;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.metamodel.SwitchEntryMetaModel;
import java.util.Optional;

/**
 * <h1>One case in a switch statement</h1>
 * The main Javadoc is in {@link SwitchStmt}
 * <h2>Java 1.0-11</h2>
 * <pre>{@code
 * switch (i) {
 *   case 1:
 *   case 2:
 *     System.out.println(444);
 *     break;
 *   default:
 *     System.out.println(0);
 * }
 * }</pre>
 * <br>
 * This contains three SwitchEntrys. All of them are of type STATEMENT_GROUP.
 * <ul>
 *     <li>The first one has label 1 and no statements.</li>
 *     <li>The second has label 2 and two statements (the println and the break).</li>
 *     <li>The third, the default, has no label and one statement.</li>
 * </ul>
 * <h2>Java 12-</h2>
 * <pre>{@code
 *     case 1 -> 15*15;
 *     case 2 -> { a++; b++; }
 *     case 3 -> throw new Exception();
 * }</pre>
 * These are three new variants.
 * <ul>
 *     <li>The first one is of type EXPRESSION and stores its {@link Expression} in an {@link ExpressionStmt} which is stored as the first and only statement in statements.</li>
 *     <li>The second one is of type BLOCK and stores its {@link BlockStmt} as the first and only statement in statements.</li>
 *     <li>The third one is of type THROWS_STATEMENT and stores its {@link ThrowStmt} as the first and only statement in statements.</li>
 * </ul>
 * <pre>{@code
 *     case MONDAY, FRIDAY, SUNDAY -> 6;
 * }</pre>
 * Multiple case labels are now allowed.
 * <pre>{@code
 *     case 16*16, 10+10 -> 6;
 * }</pre>
 * Many kinds of expressions are now allowed.
 *
 * Note (https://github.com/javaparser/javaparser/pull/4679):
 * The JavaParser representation for SwitchEntry is (slightly) incorrect.
 * JP Assumes that the body of a SwitchEntry will be a list of statements which was true before switch expressions were added, but is no longer the case for this rule.
 *
 * The workaround for this was to wrap the expression in an ExpressionStmt node which works well, but is not entirely correct according to the JLS since the ExpressionStmt in this specific case can contain any expression,
 * not just those which are legal expression statements according to the JLS, for example below (a lambda is not a valid expression statement, but the below snippet is still legal Java code):
 * <pre>{@code
 *      return switch (o) {
 *          case String s -> (arg) -> System.out.println(arg + s);
 *          case null, default -> (arg) -> {};
 *      };
 * }</pre>
 * https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.28
 * https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.8
 *
 * @author Julio Vilmar Gesser
 * @see SwitchStmt
 * @see com.github.javaparser.ast.expr.SwitchExpr
 */
public class SwitchEntry extends Node implements NodeWithStatements<SwitchEntry> {

    public enum Type {
        STATEMENT_GROUP,
        EXPRESSION,
        BLOCK,
        THROWS_STATEMENT
    }

    private NodeList<Expression> labels;

    private NodeList<Statement> statements;

    private Type type;

    private boolean isDefault;

    @OptionalProperty
    private Expression guard;

    public SwitchEntry() {
        this(null, new NodeList<Expression>(), Type.STATEMENT_GROUP, new NodeList<>(), false, null);
    }

    /**
     * This constructor exists for backwards compatibility for code that instantiated `SwitchEntries` before
     * the `isDefault` and guard fields were added.
     */
    public SwitchEntry(
            final TokenRange tokenRange,
            final NodeList<Expression> labels,
            final Type type,
            final NodeList<Statement> statements) {
        this(tokenRange, labels, type, statements, false, null);
    }

    /**
     * This constructor exists for backwards compatibility for code that instantiated `SwitchEntries` before
     * the `isDefault` and guard fields were added.
     */
    public SwitchEntry(final NodeList<Expression> labels, final Type type, final NodeList<Statement> statements) {
        this(null, labels, type, statements, false, null);
    }

    @AllFieldsConstructor
    public SwitchEntry(
            final NodeList<Expression> labels,
            final Type type,
            final NodeList<Statement> statements,
            final boolean isDefault,
            final Expression guard) {
        this(null, labels, type, statements, isDefault, guard);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SwitchEntry(
            TokenRange tokenRange,
            NodeList<Expression> labels,
            Type type,
            NodeList<Statement> statements,
            boolean isDefault,
            Expression guard) {
        super(tokenRange);
        setLabels(labels);
        setType(type);
        setStatements(statements);
        setDefault(isDefault);
        setGuard(guard);
        customInitialization();
    }

    /**
     * This is required for the ConcreteSyntaxModel, specifically to determine whether this
     * entry uses the classic switch statement syntax (e.g. `case X: ...`) or the newer
     * switch expression syntax (`case X -> ...`).
     *
     * The entry type is STATEMENT_GROUP in the switch statement case and all other values
     * are for the various switch expressions.
     */
    @DerivedProperty
    public boolean isSwitchStatementEntry() {
        return type == Type.STATEMENT_GROUP;
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
    public NodeList<Expression> getLabels() {
        return labels;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Statement> getStatements() {
        return statements;
    }

    /**
     * Sets the label
     *
     * @param labels the label, can be null
     * @return this, the SwitchEntry
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntry setLabels(final NodeList<Expression> labels) {
        assertNotNull(labels);
        if (labels == this.labels) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.LABELS, this.labels, labels);
        if (this.labels != null) this.labels.setParentNode(null);
        this.labels = labels;
        setAsParentNodeOf(labels);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntry setStatements(final NodeList<Statement> statements) {
        assertNotNull(statements);
        if (statements == this.statements) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.STATEMENTS, this.statements, statements);
        if (this.statements != null) this.statements.setParentNode(null);
        this.statements = statements;
        setAsParentNodeOf(statements);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (guard != null) {
            if (node == guard) {
                removeGuard();
                return true;
            }
        }
        for (int i = 0; i < labels.size(); i++) {
            if (labels.get(i) == node) {
                labels.remove(i);
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public SwitchEntry clone() {
        return (SwitchEntry) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public SwitchEntryMetaModel getMetaModel() {
        return JavaParserMetaModel.switchEntryMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntry setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (guard != null) {
            if (node == guard) {
                setGuard((Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < labels.size(); i++) {
            if (labels.get(i) == node) {
                labels.set(i, (Expression) replacementNode);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isDefault() {
        return isDefault;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntry setDefault(final boolean isDefault) {
        if (isDefault == this.isDefault) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.DEFAULT, this.isDefault, isDefault);
        this.isDefault = isDefault;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getGuard() {
        return Optional.ofNullable(guard);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SwitchEntry setGuard(final Expression guard) {
        if (guard == this.guard) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.GUARD, this.guard, guard);
        if (this.guard != null) this.guard.setParentNode(null);
        this.guard = guard;
        setAsParentNodeOf(guard);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public SwitchEntry removeGuard() {
        return setGuard((Expression) null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SwitchEntry(
            TokenRange tokenRange,
            NodeList<Expression> labels,
            Type type,
            NodeList<Statement> statements,
            boolean isDefault) {
        super(tokenRange);
        setLabels(labels);
        setType(type);
        setStatements(statements);
        setDefault(isDefault);
        customInitialization();
    }
}
