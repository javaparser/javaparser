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
package com.github.javaparser.ast.body;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithExtends;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.*;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ClassOrInterfaceDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A definition of a class or interface.<br/><code>class X { ... }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceDeclaration extends TypeDeclaration<ClassOrInterfaceDeclaration> implements NodeWithImplements<ClassOrInterfaceDeclaration>, NodeWithExtends<ClassOrInterfaceDeclaration>, NodeWithTypeParameters<ClassOrInterfaceDeclaration> {

    private boolean isInterface;

    private NodeList<TypeParameter> typeParameters;

    // Can contain more than one item if this is an interface
    private NodeList<ClassOrInterfaceType> extendedTypes;

    private NodeList<ClassOrInterfaceType> implementedTypes;

    public ClassOrInterfaceDeclaration() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), false, new SimpleName(), new NodeList<>(), new NodeList<>(), new NodeList<>(), new NodeList<>());
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers, final boolean isInterface, final String name) {
        this(null, modifiers, new NodeList<>(), isInterface, new SimpleName(name), new NodeList<>(), new NodeList<>(), new NodeList<>(), new NodeList<>());
    }

    @AllFieldsConstructor
    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final boolean isInterface, final SimpleName name, final NodeList<TypeParameter> typeParameters, final NodeList<ClassOrInterfaceType> extendedTypes, final NodeList<ClassOrInterfaceType> implementedTypes, final NodeList<BodyDeclaration<?>> members) {
        this(null, modifiers, annotations, isInterface, name, typeParameters, extendedTypes, implementedTypes, members);
    }

    public ClassOrInterfaceDeclaration(Range range, final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final boolean isInterface, final SimpleName name, final NodeList<TypeParameter> typeParameters, final NodeList<ClassOrInterfaceType> extendedTypes, final NodeList<ClassOrInterfaceType> implementedTypes, final NodeList<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
        setInterface(isInterface);
        setTypeParameters(typeParameters);
        setExtendedTypes(extendedTypes);
        setImplementedTypes(implementedTypes);
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
    public NodeList<ClassOrInterfaceType> getExtendedTypes() {
        return extendedTypes;
    }

    @Override
    public NodeList<ClassOrInterfaceType> getImplementedTypes() {
        return implementedTypes;
    }

    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    public boolean isInterface() {
        return isInterface;
    }

    @Override
    public ClassOrInterfaceDeclaration setExtendedTypes(final NodeList<ClassOrInterfaceType> extendedTypes) {
        assertNotNull(extendedTypes);
        notifyPropertyChange(ObservableProperty.EXTENDED_TYPES, this.extendedTypes, extendedTypes);
        if (this.extendedTypes != null)
            this.extendedTypes.setParentNode(null);
        this.extendedTypes = extendedTypes;
        setAsParentNodeOf(extendedTypes);
        return this;
    }

    @Override
    public ClassOrInterfaceDeclaration setImplementedTypes(final NodeList<ClassOrInterfaceType> implementedTypes) {
        assertNotNull(implementedTypes);
        notifyPropertyChange(ObservableProperty.IMPLEMENTED_TYPES, this.implementedTypes, implementedTypes);
        if (this.implementedTypes != null)
            this.implementedTypes.setParentNode(null);
        this.implementedTypes = implementedTypes;
        setAsParentNodeOf(implementedTypes);
        return this;
    }

    public ClassOrInterfaceDeclaration setInterface(final boolean isInterface) {
        notifyPropertyChange(ObservableProperty.INTERFACE, this.isInterface, isInterface);
        this.isInterface = isInterface;
        return this;
    }

    @Override
    public ClassOrInterfaceDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        assertNotNull(typeParameters);
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        if (this.typeParameters != null)
            this.typeParameters.setParentNode(null);
        this.typeParameters = typeParameters;
        setAsParentNodeOf(typeParameters);
        return this;
    }

    /**
     * Try to find a {@link ConstructorDeclaration} with no parameters by its name
     *
     * @return the methods found (multiple in case of polymorphism)
     */
    public Optional<ConstructorDeclaration> getDefaultConstructor() {
        return getMembers().stream().filter(bd -> bd instanceof ConstructorDeclaration).map(bd -> (ConstructorDeclaration) bd).filter(cd -> cd.getParameters().isEmpty()).findFirst();
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getExtendedTypes(), getImplementedTypes(), getTypeParameters(), getMembers(), getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < extendedTypes.size(); i++) {
            if (extendedTypes.get(i) == node) {
                extendedTypes.remove(i);
                return true;
            }
        }
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.remove(i);
                return true;
            }
        }
        for (int i = 0; i < typeParameters.size(); i++) {
            if (typeParameters.get(i) == node) {
                typeParameters.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public ClassOrInterfaceDeclaration clone() {
        return (ClassOrInterfaceDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public ClassOrInterfaceDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.classOrInterfaceDeclarationMetaModel;
    }
}
