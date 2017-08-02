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
package com.github.javaparser.ast.type;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.TypeMetaModel;
import static com.github.javaparser.utils.Utils.assertNotNull;

import javax.annotation.Generated;
import com.github.javaparser.TokenRange;

import java.util.List;

/**
 * Base class for types.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Type extends Node {

    private List<ArrayType.ArrayBracketPair> arrayBracketPairs;

    private NodeList<AnnotationExpr> annotations;

    /**
     * Several sub classes do not support annotations.
     * This is a support constructor for them.
      */
    protected Type(TokenRange range) {
        this(range, new NodeList<>());
    }

    @AllFieldsConstructor
    public Type(NodeList<AnnotationExpr> annotations) {
        this(null, annotations);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public Type(TokenRange tokenRange, NodeList<AnnotationExpr> annotations) {
        super(tokenRange);
        setAnnotations(annotations);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public AnnotationExpr getAnnotation(int i) {
        return getAnnotations().get(i);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        if (annotations == this.annotations) {
            return (Type) this;
        }
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    /**
     * Finds the element type, meaning: the type without ArrayTypes around it.
     * <p>
     * In "<code>int[] a[];</code>", the element type is int.
     */
    public Type getElementType() {
        if (this instanceof ArrayType) {
            return ((ArrayType) this).getComponentType().getElementType();
        }
        return this;
    }

    public int getArrayLevel() {
        if (this instanceof ArrayType) {
            return 1 + ((ArrayType) this).getComponentType().getArrayLevel();
        } else {
            return 0;
        }
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    public abstract String asString();

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public Type clone() {
        return (Type) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public TypeMetaModel getMetaModel() {
        return JavaParserMetaModel.typeMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    /**
     * Finds the list of annotations at the particular array level of the type and returns it.
     * Throws the IllegalArgumentException if specified level is greater then maximal level
     * of the array in this type or less then 0.
     * @param level the array level which annotations should be returned.
     * @return the annotations at the particular array level.
     */
    public List<AnnotationExpr> getAnnotationsAtLevel(int level) {
        if (level >= getArrayCount() || level < 0) {
            throw new IllegalArgumentException("The level argument should be greater then 0 and" +
                    "less then the array count (" + getArrayCount() + "). Specified level is " + level);
        }
        return arrayBracketPairs.get(level).getAnnotations();
    }

    public List<ArrayType.ArrayBracketPair> getArrayBracketPairs() {
        return arrayBracketPairs;
    }

    public Type setArrayBracketPairs(List<ArrayType.ArrayBracketPair> arrayBracketPairs) {
        this.arrayBracketPairs = arrayBracketPairs;
        return this;
    }

    /**
     * Checks and returns the maximum level of the array.
     * If the type is not array it should return 0.
     */
    public int getArrayCount() {
        return arrayBracketPairs == null ? 0 : arrayBracketPairs.size();
    }
}
