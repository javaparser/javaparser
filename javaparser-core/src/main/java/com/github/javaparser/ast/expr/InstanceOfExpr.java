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
package com.github.javaparser.ast.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithExpression;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.InstanceOfExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;

import java.util.Optional;
import java.util.function.Consumer;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <h1>The instanceof statement</h1>
 *
 * <h2>Java ?? to 13</h2>
 * The {@code instanceof} expression is a
 * <a href="https://docs.oracle.com/javase/specs/jls/se11/html/jls-15.html#jls-15.20">relational operator</a>,
 * evaluating to true if the object on the left hand side
 * is an instance of the type ({@link ReferenceType}) on the right hand side.
 * <br>
 * <br>
 * Example:
 * <br>{@code tool instanceof Drill}
 * <br>
 * <br>This is then used wherever a conditional/boolean value can be used. For example:
 * <br>
 * <pre>{@code if (obj instanceof String) {
 *     String s = (String) obj;
 *     // use s
 * }}</pre>
 * <br>
 * <h2>Java 14</h2>
 * Since JDK14, it is possible to bind a variable that is cast to the type being tested against.
 * This is referred to as a {@code Pattern} within <a href="https://bugs.openjdk.java.net/browse/JDK-8181287">JEP305</a>,
 * and avoids the need to cast to the desired type.
 * <br>
 * Example:
 * <br>{@code tool instanceof Drill d}
 * <br>
 * <br>This is then used wherever a conditional/boolean value can be used. The scope of the variable created can vary, and is defined further within
 * <a href="https://bugs.openjdk.java.net/browse/JDK-8181287">JEP305</a>.
 * <br>
 * <pre>{@code if (obj instanceof String s) {
 *     // can use s here
 * } else {
 *     // can't use s here
 * }}</pre>
 * <br>
 * <br>
 * <h3>JDK14 Grammar</h3>
 * Per JEP305:
 * <br>
 * <pre>{@code RelationalExpression:
 *      ...
 *      RelationalExpression instanceof ReferenceType
 *      RelationalExpression instanceof Pattern
 *
 * Pattern:
 *      ReferenceType Identifier}</pre>
 *
 * @author Julio Vilmar Gesser
 *
 * @see com.github.javaparser.ast.expr.PatternExpr
 * @see <a href="https://bugs.openjdk.java.net/browse/JDK-8181287">JEP305: https://bugs.openjdk.java.net/browse/JDK-8181287</a>
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se11/html/jls-15.html#jls-15.20">https://docs.oracle.com/javase/specs/jls/se11/html/jls-15.html#jls-15.20</a>
 */
public class InstanceOfExpr extends Expression implements NodeWithType<InstanceOfExpr, ReferenceType>, NodeWithExpression<InstanceOfExpr> {

    private Expression expression;

    @OptionalProperty
    private PatternExpr pattern;

    private ReferenceType type;

    public InstanceOfExpr() {
        this(null, new NameExpr(), new ClassOrInterfaceType(), null);
    }

    public InstanceOfExpr(final Expression expression, final ReferenceType type) {
        this(null, expression, type, null);
    }

    @AllFieldsConstructor
    public InstanceOfExpr(final Expression expression, final ReferenceType type, final PatternExpr pattern) {
        this(null, expression, type, pattern);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public InstanceOfExpr(TokenRange tokenRange, Expression expression, ReferenceType type, PatternExpr pattern) {
        super(tokenRange);
        setExpression(expression);
        setType(type);
        setPattern(pattern);
        customInitialization();
    }

    /**
     * Helper method which, if this is an expression with a pattern, returns the identifier/name.
     * <br>
     * <br>For example:
     * <br>{@code obj instanceof String stringName}
     * <br>
     * <br>In this example, {@code getName()} returns {@code stringName}
     */
    public Optional<SimpleName> getName() {
        if (pattern == null) {
            return Optional.empty();
        } else {
            return Optional.of(pattern.getName());
        }
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public InstanceOfExpr asInstanceOfExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public InstanceOfExpr clone() {
        return (InstanceOfExpr) accept(new CloneVisitor(), null);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public InstanceOfExprMetaModel getMetaModel() {
        return JavaParserMetaModel.instanceOfExprMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<PatternExpr> getPattern() {
        return Optional.ofNullable(pattern);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ReferenceType getType() {
        return type;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifInstanceOfExpr(Consumer<InstanceOfExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isInstanceOfExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (pattern != null) {
            if (node == pattern) {
                removePattern();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public InstanceOfExpr removePattern() {
        return setPattern((PatternExpr) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        if (pattern != null) {
            if (node == pattern) {
                setPattern((PatternExpr) replacementNode);
                return true;
            }
        }
        if (node == type) {
            setType((ReferenceType) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public InstanceOfExpr setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public InstanceOfExpr setPattern(final PatternExpr pattern) {
        if (pattern == this.pattern) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PATTERN, this.pattern, pattern);
        if (this.pattern != null)
            this.pattern.setParentNode(null);
        this.pattern = pattern;
        setAsParentNodeOf(pattern);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public InstanceOfExpr setType(final ReferenceType type) {
        assertNotNull(type);
        if (type == this.type) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<InstanceOfExpr> toInstanceOfExpr() {
        return Optional.of(this);
    }
}
