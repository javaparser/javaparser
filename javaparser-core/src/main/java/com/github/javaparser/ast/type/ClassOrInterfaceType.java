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
package com.github.javaparser.ast.type;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.ClassOrInterfaceTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.stream.Collectors.joining;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import java.util.function.Consumer;
import com.github.javaparser.ast.Generated;

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
public class ClassOrInterfaceType extends ReferenceType implements NodeWithSimpleName<ClassOrInterfaceType>, NodeWithAnnotations<ClassOrInterfaceType>, NodeWithTypeArguments<ClassOrInterfaceType> {

    @OptionalProperty
    private ClassOrInterfaceType scope;

    private SimpleName name;

    @OptionalProperty
    private NodeList<Type> typeArguments;

    public ClassOrInterfaceType() {
        this(null, null, new SimpleName(), null, new NodeList<>());
    }

    /**
     * @deprecated use JavaParser.parseClassOrInterfaceType instead. This constructor does not understand generics.
     */
    public ClassOrInterfaceType(final String name) {
        this(null, null, new SimpleName(name), null, new NodeList<>());
    }

    public ClassOrInterfaceType(final ClassOrInterfaceType scope, final String name) {
        this(null, scope, new SimpleName(name), null, new NodeList<>());
    }

    public ClassOrInterfaceType(final ClassOrInterfaceType scope, final SimpleName name, final NodeList<Type> typeArguments) {
        this(null, scope, name, typeArguments, new NodeList<>());
    }

    @AllFieldsConstructor
    public ClassOrInterfaceType(final ClassOrInterfaceType scope, final SimpleName name, final NodeList<Type> typeArguments, final NodeList<AnnotationExpr> annotations) {
        this(null, scope, name, typeArguments, annotations);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ClassOrInterfaceType(TokenRange tokenRange, ClassOrInterfaceType scope, SimpleName name, NodeList<Type> typeArguments, NodeList<AnnotationExpr> annotations) {
        super(tokenRange, annotations);
        this.setScope(scope);
        this.setName(name);
        this.setTypeArguments(typeArguments);
        this.customInitialization();
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return this.name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<ClassOrInterfaceType> getScope() {
        return Optional.ofNullable(this.scope);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassOrInterfaceType setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null) {
            this.name.setParentNode(null);
        }
        this.name = name;
        this.setAsParentNodeOf(name);
        return this;
    }

    /**
     * Sets the scope
     *
     * @param scope the scope, can be null
     * @return this, the ClassOrInterfaceType
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassOrInterfaceType setScope(final ClassOrInterfaceType scope) {
        if (scope == this.scope) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        if (this.scope != null) {
            this.scope.setParentNode(null);
        }
        this.scope = scope;
        this.setAsParentNodeOf(scope);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(this.typeArguments);
    }

    /**
     * Sets the typeArguments
     *
     * @param typeArguments the typeArguments, can be null
     * @return this, the ClassOrInterfaceType
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassOrInterfaceType setTypeArguments(final NodeList<Type> typeArguments) {
        if (typeArguments == this.typeArguments) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        if (this.typeArguments != null) {
            this.typeArguments.setParentNode(null);
        }
        this.typeArguments = typeArguments;
        this.setAsParentNodeOf(typeArguments);
        return this;
    }

    @Override
    public ClassOrInterfaceType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (ClassOrInterfaceType) super.setAnnotations(annotations);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (this.scope != null) {
            if (node == this.scope) {
                this.removeScope();
                return true;
            }
        }
        if (this.typeArguments != null) {
            for (int i = 0; i < this.typeArguments.size(); i++) {
                if (this.typeArguments.get(i) == node) {
                    this.typeArguments.remove(i);
                    return true;
                }
            }
        }
        return super.remove(node);
    }

    @Override
    public String asString() {
        StringBuilder str = new StringBuilder();
        getScope().ifPresent(s -> str.append(s.asString()).append("."));
        str.append(name.asString());
        getTypeArguments().ifPresent(ta -> str.append(ta.stream().map(Type::asString).collect(joining(",", "<", ">"))));
        return str.toString();
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public ClassOrInterfaceType removeScope() {
        return this.setScope((ClassOrInterfaceType) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ClassOrInterfaceType clone() {
        return (ClassOrInterfaceType) this.accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ClassOrInterfaceTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.classOrInterfaceTypeMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == this.name) {
            this.setName((SimpleName) replacementNode);
            return true;
        }
        if (this.scope != null) {
            if (node == this.scope) {
                this.setScope((ClassOrInterfaceType) replacementNode);
                return true;
            }
        }
        if (this.typeArguments != null) {
            for (int i = 0; i < this.typeArguments.size(); i++) {
                if (this.typeArguments.get(i) == node) {
                    this.typeArguments.set(i, (Type) replacementNode);
                    return true;
                }
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isClassOrInterfaceType() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ClassOrInterfaceType asClassOrInterfaceType() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifClassOrInterfaceType(Consumer<ClassOrInterfaceType> action) {
        action.accept(this);
    }

    @Override
    public ResolvedReferenceType resolve() {
        return getSymbolResolver().toResolvedType(this, ResolvedReferenceType.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ClassOrInterfaceType> toClassOrInterfaceType() {
        return Optional.of(this);
    }
}
