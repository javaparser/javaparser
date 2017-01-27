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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A class or an interface type. <br/><code>Object</code> <br/><code>HashMap&lt;String, String></code>
 * <br/><code>java.util.Punchcard</code>
 * <p>
 * <p>Note that the syntax is ambiguous here, and JavaParser does not know what is to the left of the class. It assumes
 * cases like <code>Map.Entry</code> where Map is the scope of Entry. In <code>java.util.Punchcard</code>, it will not
 * recognize that java and util are parts of the package name. Instead, it will set util as the scope of Punchcard, as a
 * ClassOrInterfaceType (which it is not.) In turn, util will have java as its scope, also as a
 * ClassOrInterfaceType</p>
 *
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceType extends ReferenceType implements
        NodeWithSimpleName<ClassOrInterfaceType>,
        NodeWithAnnotations<ClassOrInterfaceType>,
        NodeWithTypeArguments<ClassOrInterfaceType> {

    private ClassOrInterfaceType scope;

    private SimpleName name;

    private NodeList<Type> typeArguments;

    public ClassOrInterfaceType() {
        this(null,
                null,
                new SimpleName(),
                null);
    }

    public ClassOrInterfaceType(final String name) {
        this(null,
                null,
                new SimpleName(name),
                null);
    }

    public ClassOrInterfaceType(final ClassOrInterfaceType scope, final String name) {
        this(null,
                scope,
                new SimpleName(name),
                null);
    }

    public ClassOrInterfaceType(final Range range, final ClassOrInterfaceType scope, final SimpleName name,
                                final NodeList<Type> typeArguments) {
        super(range);
        setScope(scope);
        setName(name);
        setTypeArguments(typeArguments);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    public Optional<ClassOrInterfaceType> getScope() {
        return Optional.ofNullable(scope);
    }

    public boolean isBoxedType() {
        return PrimitiveType.unboxMap.containsKey(name.getIdentifier());
    }

    public PrimitiveType toUnboxedType() throws UnsupportedOperationException {
        if (!isBoxedType()) {
            throw new UnsupportedOperationException(name + " isn't a boxed type.");
        }
        return new PrimitiveType(PrimitiveType.unboxMap.get(name.getIdentifier()));
    }

    @Override
    public ClassOrInterfaceType setName(final SimpleName name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
        return this;
    }

    /**
     * Sets the scope
     *
     * @param scope the scope, can be null
     * @return this, the ClassOrInterfaceType
     */
    public ClassOrInterfaceType setScope(final ClassOrInterfaceType scope) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the typeArguments
     *
     * @param typeArguments the typeArguments, can be null
     * @return this, the ClassOrInterfaceType
     */
    @Override
    public ClassOrInterfaceType setTypeArguments(final NodeList<Type> typeArguments) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }

    @Override
    public ClassOrInterfaceType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (ClassOrInterfaceType) super.setAnnotations(annotations);
    }
}
