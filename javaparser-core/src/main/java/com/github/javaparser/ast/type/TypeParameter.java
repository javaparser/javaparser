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

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.TypeParameterMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A type parameter.
 * <br/><code>&lt;<b>U</b>> U getU() { ... }</code>
 * <br/><code>class D &lt;<b>@Brain T extends B & A & @Tripe C</b>> { ... }</code>
 * <p>U and T are type parameter names.
 * <br/>B, A, and C are type parameter bounds.
 * <br/>Tripe is an annotation on type parameter bound C.
 * <br/>Brain is an annotation on type parameter T.
 *
 * @author Julio Vilmar Gesser
 * @see com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters
 */
public final class TypeParameter extends ReferenceType<TypeParameter> implements NodeWithSimpleName<TypeParameter>, NodeWithAnnotations<TypeParameter> {

    private SimpleName name;

    private NodeList<ClassOrInterfaceType> typeBound;

    public TypeParameter() {
        this(null, new SimpleName(), new NodeList<>(), new NodeList<>());
    }

    public TypeParameter(final String name) {
        this(null, new SimpleName(name), new NodeList<>(), new NodeList<>());
    }

    public TypeParameter(final String name, final NodeList<ClassOrInterfaceType> typeBound) {
        this(null, new SimpleName(name), typeBound, new NodeList<>());
    }

    public TypeParameter(Range range, final SimpleName name, final NodeList<ClassOrInterfaceType> typeBound) {
        this(range, name, typeBound, new NodeList<>());
    }

    @AllFieldsConstructor
    public TypeParameter(SimpleName name, NodeList<ClassOrInterfaceType> typeBound, NodeList<AnnotationExpr> annotations) {
        this(null, name, typeBound, annotations);
    }

    public TypeParameter(Range range, SimpleName name, NodeList<ClassOrInterfaceType> typeBound, NodeList<AnnotationExpr> annotations) {
        super(range);
        setName(name);
        setTypeBound(typeBound);
        setAnnotations(annotations);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * Return the name of the paramenter.
     *
     * @return the name of the paramenter
     */
    @Override
    public SimpleName getName() {
        return name;
    }

    /**
     * Return the list of {@link ClassOrInterfaceType} that this parameter
     * extends. Return <code>null</code> null if there are no type.
     *
     * @return list of types that this paramente extends or <code>null</code>
     */
    public NodeList<ClassOrInterfaceType> getTypeBound() {
        return typeBound;
    }

    @Override
    public TypeParameter setName(final SimpleName name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    public TypeParameter setTypeBound(final NodeList<ClassOrInterfaceType> typeBound) {
        assertNotNull(typeBound);
        notifyPropertyChange(ObservableProperty.TYPE_BOUND, this.typeBound, typeBound);
        if (this.typeBound != null)
            this.typeBound.setParentNode(null);
        this.typeBound = typeBound;
        setAsParentNodeOf(typeBound);
        return this;
    }

    @Override
    public TypeParameter setAnnotations(NodeList<AnnotationExpr> annotations) {
        super.setAnnotations(annotations);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getTypeBound(), getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < typeBound.size(); i++) {
            if (typeBound.get(i) == node) {
                typeBound.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public TypeParameter clone() {
        return (TypeParameter) accept(new CloneVisitor(), null);
    }

    @Override
    public TypeParameterMetaModel getMetaModel() {
        return JavaParserMetaModel.typeParameterMetaModel;
    }
}
