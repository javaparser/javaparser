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

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.EnumConstantDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import java.util.function.Consumer;
import java.util.Optional;
import com.github.javaparser.ast.Generated;

/**
 * One of the values an enum can take. A(1) and B(2) in this example: <code>enum X { A(1), B(2) }</code>
 *
 * @author Julio Vilmar Gesser
 */
public class EnumConstantDeclaration extends BodyDeclaration<EnumConstantDeclaration> implements NodeWithJavadoc<EnumConstantDeclaration>, NodeWithSimpleName<EnumConstantDeclaration>, NodeWithArguments<EnumConstantDeclaration>, Resolvable<ResolvedEnumConstantDeclaration> {

    private SimpleName name;

    private NodeList<Expression> arguments;

    private NodeList<BodyDeclaration<?>> classBody;

    public EnumConstantDeclaration() {
        this(null, new NodeList<>(), new SimpleName(), new NodeList<>(), new NodeList<>());
    }

    public EnumConstantDeclaration(String name) {
        this(null, new NodeList<>(), new SimpleName(name), new NodeList<>(), new NodeList<>());
    }

    @AllFieldsConstructor
    public EnumConstantDeclaration(NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Expression> arguments, NodeList<BodyDeclaration<?>> classBody) {
        this(null, annotations, name, arguments, classBody);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public EnumConstantDeclaration(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Expression> arguments, NodeList<BodyDeclaration<?>> classBody) {
        super(tokenRange, annotations);
        setName(name);
        setArguments(arguments);
        setClassBody(classBody);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<BodyDeclaration<?>> getClassBody() {
        return classBody;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumConstantDeclaration setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
        if (arguments == this.arguments) {
            return (EnumConstantDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        if (this.arguments != null)
            this.arguments.setParentNode(null);
        this.arguments = arguments;
        setAsParentNodeOf(arguments);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumConstantDeclaration setClassBody(final NodeList<BodyDeclaration<?>> classBody) {
        assertNotNull(classBody);
        if (classBody == this.classBody) {
            return (EnumConstantDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.CLASS_BODY, this.classBody, classBody);
        if (this.classBody != null)
            this.classBody.setParentNode(null);
        this.classBody = classBody;
        setAsParentNodeOf(classBody);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumConstantDeclaration setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return (EnumConstantDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.remove(i);
                return true;
            }
        }
        for (int i = 0; i < classBody.size(); i++) {
            if (classBody.get(i) == node) {
                classBody.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public EnumConstantDeclaration clone() {
        return (EnumConstantDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public EnumConstantDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.enumConstantDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < classBody.size(); i++) {
            if (classBody.get(i) == node) {
                classBody.set(i, (BodyDeclaration) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumConstantDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumConstantDeclaration asEnumConstantDeclaration() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumConstantDeclaration(Consumer<EnumConstantDeclaration> action) {
        action.accept(this);
    }

    @Override
    public ResolvedEnumConstantDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedEnumConstantDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnumConstantDeclaration> toEnumConstantDeclaration() {
        return Optional.of(this);
    }
}
