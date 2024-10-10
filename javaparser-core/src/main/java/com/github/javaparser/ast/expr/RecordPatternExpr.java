/*
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
package com.github.javaparser.ast.expr;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.RecordPatternExprMetaModel;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * <h1>Record Patterns</h1>
 * Record patterns were officially added in Java 21 to allow the deconstruction of
 * record values and provide convenient access to inner fields through pattern matching.
 * <br>
 * <br>
 * <h3>JDK 21 Grammar</h3>
 * <pre><code>Pattern
 *     TypePattern
 *     RecordPattern
 *
 * RecordPattern:
 *     ReferenceType ( [PatternList] )
 *
 * PatternList
 *     Pattern {, Pattern }
 * </code></pre>
 *
 * <h3>Example</h3>
 * Example taken from <a href="https://openjdk.org/jeps/440">JEP440: RecordPatterns</a>
 * <pre><code>
 *  record Pair(Object x, Object y) {}
 *
 * Pair p = new Pair(42, 42);
 *
 * if (p instanceof Pair(String s, String t)) {
 *     System.out.println(s + ", " + t);
 * } else {
 *     System.out.println("Not a pair of strings");
 * }
 * </code></pre>
 *
 * @see com.github.javaparser.ast.expr.PatternExpr
 * @see com.github.javaparser.ast.expr.TypePatternExpr
 * @see <a href="https://openjdk.org/jeps/440">JEP 440: Record Patterns</a>
 */
public class RecordPatternExpr extends PatternExpr implements NodeWithFinalModifier<RecordPatternExpr> {

    private NodeList<Modifier> modifiers;

    private NodeList<PatternExpr> patternList;

    public RecordPatternExpr() {
        this(new NodeList<>(), new ClassOrInterfaceType(), new NodeList<>());
    }

    @AllFieldsConstructor
    public RecordPatternExpr(
            final NodeList<Modifier> modifiers, final Type type, final NodeList<PatternExpr> patternList) {
        this(null, modifiers, type, patternList);
    }

    /**
     * The type of RecordPatternExpr must always be a reference type. Only nested TypePatternExprs may have primitive
     * types.
     */
    @Override
    public ReferenceType getType() {
        return super.getType().asReferenceType();
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
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordPatternExpr setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null) this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isRecordPatternExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public RecordPatternExpr asRecordPatternExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<RecordPatternExpr> toRecordPatternExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifRecordPatternExpr(Consumer<RecordPatternExpr> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<PatternExpr> getPatternList() {
        return patternList;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordPatternExpr setPatternList(final NodeList<PatternExpr> patternList) {
        assertNotNull(patternList);
        if (patternList == this.patternList) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PATTERN_LIST, this.patternList, patternList);
        if (this.patternList != null) this.patternList.setParentNode(null);
        this.patternList = patternList;
        setAsParentNodeOf(patternList);
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
        for (int i = 0; i < patternList.size(); i++) {
            if (patternList.get(i) == node) {
                patternList.remove(i);
                return true;
            }
        }
        return super.remove(node);
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
        for (int i = 0; i < patternList.size(); i++) {
            if (patternList.get(i) == node) {
                patternList.set(i, (PatternExpr) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public RecordPatternExpr clone() {
        return (RecordPatternExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public RecordPatternExprMetaModel getMetaModel() {
        return JavaParserMetaModel.recordPatternExprMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public RecordPatternExpr(
            TokenRange tokenRange, NodeList<Modifier> modifiers, Type type, NodeList<PatternExpr> patternList) {
        super(tokenRange, type);
        setModifiers(modifiers);
        setPatternList(patternList);
        customInitialization();
    }
}
