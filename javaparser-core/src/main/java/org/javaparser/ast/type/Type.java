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

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.expr.AnnotationExpr;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.metamodel.TypeMetaModel;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.TokenRange;
import org.javaparser.resolution.Resolvable;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.ast.Generated;
import java.util.function.Consumer;
import static org.javaparser.utils.CodeGenerationUtils.f;
import java.util.Optional;

/**
 * Base class for types.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Type extends Node implements Resolvable<ResolvedType> {

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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public Type(TokenRange tokenRange, NodeList<AnnotationExpr> annotations) {
        super(tokenRange);
        setAnnotations(annotations);
        customInitialization();
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public AnnotationExpr getAnnotation(int i) {
        return getAnnotations().get(i);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
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
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public Type clone() {
        return (Type) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public TypeMetaModel getMetaModel() {
        return JavaParserMetaModel.typeMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
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

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayType asArrayType() {
        throw new IllegalStateException(f("%s is not an ArrayType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isClassOrInterfaceType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ClassOrInterfaceType asClassOrInterfaceType() {
        throw new IllegalStateException(f("%s is not an ClassOrInterfaceType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isIntersectionType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public IntersectionType asIntersectionType() {
        throw new IllegalStateException(f("%s is not an IntersectionType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isPrimitiveType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public PrimitiveType asPrimitiveType() {
        throw new IllegalStateException(f("%s is not an PrimitiveType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isReferenceType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ReferenceType asReferenceType() {
        throw new IllegalStateException(f("%s is not an ReferenceType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTypeParameter() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public TypeParameter asTypeParameter() {
        throw new IllegalStateException(f("%s is not an TypeParameter", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isUnionType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public UnionType asUnionType() {
        throw new IllegalStateException(f("%s is not an UnionType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isUnknownType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public UnknownType asUnknownType() {
        throw new IllegalStateException(f("%s is not an UnknownType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isVoidType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public VoidType asVoidType() {
        throw new IllegalStateException(f("%s is not an VoidType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isWildcardType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public WildcardType asWildcardType() {
        throw new IllegalStateException(f("%s is not an WildcardType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayType(Consumer<ArrayType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifClassOrInterfaceType(Consumer<ClassOrInterfaceType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifIntersectionType(Consumer<IntersectionType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifPrimitiveType(Consumer<PrimitiveType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifReferenceType(Consumer<ReferenceType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTypeParameter(Consumer<TypeParameter> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnionType(Consumer<UnionType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnknownType(Consumer<UnknownType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifVoidType(Consumer<VoidType> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifWildcardType(Consumer<WildcardType> action) {
    }

    @Override
    public abstract ResolvedType resolve();

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayType> toArrayType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ClassOrInterfaceType> toClassOrInterfaceType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<IntersectionType> toIntersectionType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<PrimitiveType> toPrimitiveType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ReferenceType> toReferenceType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TypeParameter> toTypeParameter() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<UnionType> toUnionType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<UnknownType> toUnknownType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<VoidType> toVoidType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<WildcardType> toWildcardType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isVarType() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public VarType asVarType() {
        throw new IllegalStateException(f("%s is not an VarType", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<VarType> toVarType() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifVarType(Consumer<VarType> action) {
    }
}
