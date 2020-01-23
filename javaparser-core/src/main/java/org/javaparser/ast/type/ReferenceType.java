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
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.metamodel.ReferenceTypeMetaModel;
import org.javaparser.ast.Generated;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * Base class for reference types.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class ReferenceType extends Type {

    public ReferenceType() {
        this(null, new NodeList<>());
    }

    @AllFieldsConstructor
    public ReferenceType(NodeList<AnnotationExpr> annotations) {
        this(null, annotations);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public ReferenceType(TokenRange tokenRange, NodeList<AnnotationExpr> annotations) {
        super(tokenRange, annotations);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public ReferenceType clone() {
        return (ReferenceType) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ReferenceTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.referenceTypeMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isReferenceType() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ReferenceType asReferenceType() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifReferenceType(Consumer<ReferenceType> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ReferenceType> toReferenceType() {
        return Optional.of(this);
    }
}
