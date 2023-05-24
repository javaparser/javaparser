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
package com.github.javaparser.ast.type;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.UnknownTypeMetaModel;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.Node;

/**
 * An unknown parameter type object. It plays the role of a null object for
 * lambda parameters that have no explicit type declared. As such, it has no
 * lexical representation and hence gets no comment attributed.
 * <p>
 * <br>In {@code DoubleToIntFunction d = }<b>{@code x}</b> {@code -> (int)x + 1;} the x parameter in bold has type UnknownType.
 *
 * @author Didier Villevalois
 */
public class UnknownType extends Type {

    @AllFieldsConstructor
    public UnknownType() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public UnknownType(TokenRange tokenRange) {
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
    public UnknownType setAnnotations(NodeList<AnnotationExpr> annotations) {
        if (annotations.size() > 0) {
            throw new IllegalStateException("Inferred lambda types cannot be annotated.");
        }
        return (UnknownType) super.setAnnotations(annotations);
    }

    @Override
    public String asString() {
        return "";
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public UnknownType clone() {
        return (UnknownType) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public UnknownTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.unknownTypeMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isUnknownType() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public UnknownType asUnknownType() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnknownType(Consumer<UnknownType> action) {
        action.accept(this);
    }

    @Override
    public ResolvedType resolve() {
        return getSymbolResolver().toResolvedType(this, ResolvedReferenceType.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<UnknownType> toUnknownType() {
        return Optional.of(this);
    }

    /*
     * A "phantom" node, is a node that is not really an AST node (like the fake type of variable in FieldDeclaration)
     */
    @Override
    public boolean isPhantom() {
        return true;
    }

    /**
     * A {@link UnknownType} cannot be convertible to {@link ResolvedType}.
     *
     * @param type      The type to be converted.
     * @param context   The current context.
     *
     * @return The type resolved.
     */
    @Override
    public ResolvedType convertToUsage(Context context) {
        throw new IllegalArgumentException("Inferred lambda parameter type");
    }
}
