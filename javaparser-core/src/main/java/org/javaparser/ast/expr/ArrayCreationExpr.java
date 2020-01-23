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
package org.javaparser.ast.expr;

import org.javaparser.ast.*;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.type.ArrayType;
import org.javaparser.ast.type.ClassOrInterfaceType;
import org.javaparser.ast.type.Type;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import org.javaparser.metamodel.ArrayCreationExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.metamodel.NonEmptyProperty;
import java.util.Optional;
import static org.javaparser.StaticJavaParser.parseType;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.TokenRange;
import org.javaparser.metamodel.OptionalProperty;
import java.util.function.Consumer;
import org.javaparser.ast.Node;
import org.javaparser.ast.Generated;

/**
 * <code>new int[5][4][][]</code> or <code>new int[][]{{1},{2,3}}</code>.
 *
 * <br/>"int" is the element type.
 * <br/>All the brackets are stored in the levels field, from left to right.
 *
 * @author Julio Vilmar Gesser
 */
public class ArrayCreationExpr extends Expression {

    @NonEmptyProperty
    private NodeList<ArrayCreationLevel> levels;

    private Type elementType;

    @OptionalProperty
    private ArrayInitializerExpr initializer;

    public ArrayCreationExpr() {
        this(null, new ClassOrInterfaceType(), new NodeList<>(), new ArrayInitializerExpr());
    }

    @AllFieldsConstructor
    public ArrayCreationExpr(Type elementType, NodeList<ArrayCreationLevel> levels, ArrayInitializerExpr initializer) {
        this(null, elementType, levels, initializer);
    }

    public ArrayCreationExpr(Type elementType) {
        this(null, elementType, new NodeList<>(), new ArrayInitializerExpr());
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public ArrayCreationExpr(TokenRange tokenRange, Type elementType, NodeList<ArrayCreationLevel> levels, ArrayInitializerExpr initializer) {
        super(tokenRange);
        setElementType(elementType);
        setLevels(levels);
        setInitializer(initializer);
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
    public Optional<ArrayInitializerExpr> getInitializer() {
        return Optional.ofNullable(initializer);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Type getElementType() {
        return elementType;
    }

    /**
     * Sets the initializer
     *
     * @param initializer the initializer, can be null
     * @return this, the ArrayCreationExpr
     */
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ArrayCreationExpr setInitializer(final ArrayInitializerExpr initializer) {
        if (initializer == this.initializer) {
            return (ArrayCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.INITIALIZER, this.initializer, initializer);
        if (this.initializer != null)
            this.initializer.setParentNode(null);
        this.initializer = initializer;
        setAsParentNodeOf(initializer);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ArrayCreationExpr setElementType(final Type elementType) {
        assertNotNull(elementType);
        if (elementType == this.elementType) {
            return (ArrayCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.ELEMENT_TYPE, this.elementType, elementType);
        if (this.elementType != null)
            this.elementType.setParentNode(null);
        this.elementType = elementType;
        setAsParentNodeOf(elementType);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ArrayCreationLevel> getLevels() {
        return levels;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ArrayCreationExpr setLevels(final NodeList<ArrayCreationLevel> levels) {
        assertNotNull(levels);
        if (levels == this.levels) {
            return (ArrayCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.LEVELS, this.levels, levels);
        if (this.levels != null)
            this.levels.setParentNode(null);
        this.levels = levels;
        setAsParentNodeOf(levels);
        return this;
    }

    /**
     * Takes the element type and wraps it in an ArrayType for every array creation level.
     */
    public Type createdType() {
        Type result = elementType;
        for (int i = 0; i < levels.size(); i++) {
            result = new ArrayType(result, ArrayType.Origin.TYPE, new NodeList<>());
        }
        return result;
    }

    /**
     * Sets this type to this class and try to import it to the {@link CompilationUnit} if needed
     *
     * @param typeClass the type
     * @return this
     */
    public ArrayCreationExpr setElementType(Class<?> typeClass) {
        tryAddImportToParentCompilationUnit(typeClass);
        return setElementType(parseType(typeClass.getSimpleName()));
    }

    public ArrayCreationExpr setElementType(final String type) {
        return setElementType(parseType(type));
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (initializer != null) {
            if (node == initializer) {
                removeInitializer();
                return true;
            }
        }
        for (int i = 0; i < levels.size(); i++) {
            if (levels.get(i) == node) {
                levels.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public ArrayCreationExpr removeInitializer() {
        return setInitializer((ArrayInitializerExpr) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public ArrayCreationExpr clone() {
        return (ArrayCreationExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ArrayCreationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.arrayCreationExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == elementType) {
            setElementType((Type) replacementNode);
            return true;
        }
        if (initializer != null) {
            if (node == initializer) {
                setInitializer((ArrayInitializerExpr) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < levels.size(); i++) {
            if (levels.get(i) == node) {
                levels.set(i, (ArrayCreationLevel) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayCreationExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayCreationExpr asArrayCreationExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayCreationExpr(Consumer<ArrayCreationExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayCreationExpr> toArrayCreationExpr() {
        return Optional.of(this);
    }
}
