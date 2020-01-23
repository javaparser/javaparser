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
package org.javaparser.ast.type;

import org.javaparser.TokenRange;
import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.expr.AnnotationExpr;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.resolution.types.ResolvedType;
import java.util.Optional;
import java.util.function.Consumer;
import org.javaparser.metamodel.VarTypeMetaModel;
import org.javaparser.ast.Generated;

/**
 * <h1>A type called "var" waiting for Java to infer it.</h1>
 * Examples:
 * <ol>
 * <li><b>var</b> a = 1;</li>
 * <li><b>var</b> a = new ArrayList&lt;String>();</li>
 * </ol>
 */
public class VarType extends Type {

    @AllFieldsConstructor
    public VarType() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public VarType(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public VarType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (VarType) super.setAnnotations(annotations);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public String asString() {
        return "var";
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public VarType clone() {
        return (VarType) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public VarTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.varTypeMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    public ResolvedType resolve() {
        return getSymbolResolver().toResolvedType(this, ResolvedType.class);
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

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isVarType() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public VarType asVarType() {
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<VarType> toVarType() {
        return Optional.of(this);
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifVarType(Consumer<VarType> action) {
        action.accept(this);
    }
}
