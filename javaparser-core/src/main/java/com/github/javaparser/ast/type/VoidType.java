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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.VoidTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import com.github.javaparser.resolution.types.ResolvedUnionType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * The return type of a {@link com.github.javaparser.ast.body.MethodDeclaration}
 * when it returns void.
 * <br/><code><b>void</b> helloWorld() { ... }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class VoidType extends Type implements NodeWithAnnotations<VoidType> {

    @AllFieldsConstructor
    public VoidType() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public VoidType(TokenRange tokenRange) {
        super(tokenRange);
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

    @Override
    public VoidType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (VoidType) super.setAnnotations(annotations);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public String asString() {
        return "void";
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public VoidType clone() {
        return (VoidType) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public VoidTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.voidTypeMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isVoidType() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public VoidType asVoidType() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifVoidType(Consumer<VoidType> action) {
        action.accept(this);
    }

    @Override
    public ResolvedVoidType resolve() {
        return getSymbolResolver().toResolvedType(this, ResolvedVoidType.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<VoidType> toVoidType() {
        return Optional.of(this);
    }
}
