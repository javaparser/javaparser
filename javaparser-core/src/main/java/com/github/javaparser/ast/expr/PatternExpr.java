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
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PatternExprMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <h1>The instanceof statement</h1>
 *
 * <h2>Java 1.0 to 13</h2>
 * Not available.
 * <br>
 * <h2>Java 14</h2>
 * Since JDK14, it is possible to bind a variable that is cast to the type being tested against.
 * This is referred to as a {@code Pattern} within <a href="https://bugs.openjdk.java.net/browse/JDK-8181287">JEP305</a>,
 * and avoids the need to cast to the desired type.
 * <br>
 * Example:
 * <br>
 * <pre>{@code
 * tool instanceof Drill d
 *                 ^^^^^^^
 *                 Pattern
 * }</pre>
 * <br>Note: While this is exclusively used within {@code instanceof} operators for now, JEP305 suggests this might
 * be used more widely in the future (e.g. in switch expressions/statements).
 * <br>
 * <br>
 * <h3>JDK14 Grammar</h3>
 * Per JEP305 (not currently listed within the JLS):
 * <br>
 * <pre>{@code Pattern:
 *      ReferenceType Identifier}</pre>
 *
 * @author Roger Howell
 *
 * @see com.github.javaparser.ast.expr.InstanceOfExpr
 * @see <a href="https://bugs.openjdk.java.net/browse/JDK-8181287">JEP305: https://bugs.openjdk.java.net/browse/JDK-8181287</a>
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se11/html/jls-15.html#jls-15.20">https://docs.oracle.com/javase/specs/jls/se11/html/jls-15.html#jls-15.20</a>
 */
public class PatternExpr extends Expression implements NodeWithSimpleName<PatternExpr>, NodeWithType<PatternExpr, ReferenceType>, NodeWithFinalModifier<PatternExpr> {

    private NodeList<Modifier> modifiers;

    private SimpleName name;

    private ReferenceType type;

    public PatternExpr() {
        this(null, new NodeList<>(), new ClassOrInterfaceType(), new SimpleName());
    }

    @AllFieldsConstructor
    public PatternExpr(final NodeList<Modifier> modifiers, final ReferenceType type, SimpleName name) {
        this(null, modifiers, type, name);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public PatternExpr(TokenRange tokenRange, NodeList<Modifier> modifiers, ReferenceType type, SimpleName name) {
        super(tokenRange);
        setModifiers(modifiers);
        setType(type);
        setName(name);
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
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ReferenceType getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public PatternExpr setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public PatternExpr setType(final ReferenceType type) {
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
    public boolean isPatternExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public PatternExpr asPatternExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<PatternExpr> toPatternExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifPatternExpr(Consumer<PatternExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        if (node == type) {
            setType((ReferenceType) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public PatternExpr clone() {
        return (PatternExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public PatternExprMetaModel getMetaModel() {
        return JavaParserMetaModel.patternExprMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public PatternExpr setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }
}
