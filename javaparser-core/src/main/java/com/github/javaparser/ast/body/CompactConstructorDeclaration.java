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
package com.github.javaparser.ast.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.CompactConstructorDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <h1>The record declaration's constructor</h1>
 * <strong>WARNING: This implementation is subject to change.</strong>
 *
 * <h2>Java 1.0 to 13</h2>
 * Not available.
 * <br>
 * <h2>Java 14 (preview), Java 15 (2nd preview), Java 16</h2>
 * <p>
 * A record "compact" constructor declaration: {@code class X(int a, int b) { public X{ } }} where {@code public X{}} is the compact record constructor declaration.
 * <p>
 * Note that the record constructor is distinct from a "standard" constructor as it does not permit arguments/parameters.
 * </p>
 * <p>
 * All annotations preceding the name will be set on this object, not on the class.
 * JavaParser doesn't know if it they are applicable to the method or the class.
 * </p>
 *
 * @author Roger Howell
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se16/html/jls-8.html#jls-8.10">JLS 8.10 - Record Classes</a>
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se16/html/jls-8.html#jls-8.10.4">JLS 8.10.3 - Record Constructor Declarations</a>
 * @since 3.22.0
 */
public class CompactConstructorDeclaration extends BodyDeclaration<CompactConstructorDeclaration> implements NodeWithBlockStmt<CompactConstructorDeclaration>, NodeWithAccessModifiers<CompactConstructorDeclaration>, NodeWithJavadoc<CompactConstructorDeclaration>, NodeWithSimpleName<CompactConstructorDeclaration>, NodeWithThrownExceptions<CompactConstructorDeclaration>, NodeWithTypeParameters<CompactConstructorDeclaration>, Resolvable<ResolvedConstructorDeclaration> {

    private NodeList<Modifier> modifiers;

    private BlockStmt body;

    private NodeList<TypeParameter> typeParameters;

    private SimpleName name;

    private NodeList<ReferenceType> thrownExceptions;

    public CompactConstructorDeclaration() {
        this(null, new NodeList<>(), new NodeList<>(), new NodeList<>(), new SimpleName(), new NodeList<>(), new BlockStmt());
    }

    public CompactConstructorDeclaration(String name) {
        this(null, new NodeList<>(new Modifier()), new NodeList<>(), new NodeList<>(), new SimpleName(name), new NodeList<>(), new BlockStmt());
    }

    public CompactConstructorDeclaration(NodeList<Modifier> modifiers, String name) {
        this(null, modifiers, new NodeList<>(), new NodeList<>(), new SimpleName(name), new NodeList<>(), new BlockStmt());
    }

    @AllFieldsConstructor
    public CompactConstructorDeclaration(NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, SimpleName name, NodeList<ReferenceType> thrownExceptions, BlockStmt body) {
        this(null, modifiers, annotations, typeParameters, name, thrownExceptions, body);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public CompactConstructorDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, SimpleName name, NodeList<ReferenceType> thrownExceptions, BlockStmt body) {
        super(tokenRange, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setName(name);
        setThrownExceptions(thrownExceptions);
        setBody(body);
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
    public BlockStmt getBody() {
        return body;
    }

    /**
     * Sets the body
     *
     * @param body the body, can not be null
     * @return this, the ConstructorDeclaration
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompactConstructorDeclaration setBody(final BlockStmt body) {
        assertNotNull(body);
        if (body == this.body) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompactConstructorDeclaration setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompactConstructorDeclaration setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ReferenceType> getThrownExceptions() {
        return thrownExceptions;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompactConstructorDeclaration setThrownExceptions(final NodeList<ReferenceType> thrownExceptions) {
        assertNotNull(thrownExceptions);
        if (thrownExceptions == this.thrownExceptions) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.THROWN_EXCEPTIONS, this.thrownExceptions, thrownExceptions);
        if (this.thrownExceptions != null)
            this.thrownExceptions.setParentNode(null);
        this.thrownExceptions = thrownExceptions;
        setAsParentNodeOf(thrownExceptions);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompactConstructorDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        assertNotNull(typeParameters);
        if (typeParameters == this.typeParameters) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        if (this.typeParameters != null)
            this.typeParameters.setParentNode(null);
        this.typeParameters = typeParameters;
        setAsParentNodeOf(typeParameters);
        return this;
    }

    /**
     * The declaration returned has this schema:
     * <p>
     * [accessSpecifier] className [throws exceptionsList]
     */
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows, boolean includingParameterName) {
        StringBuilder sb = new StringBuilder();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = getAccessSpecifier();
            sb.append(accessSpecifier.asString()).append(" ");
        }
        sb.append(getName());
        sb.append("(");
        boolean firstParam = true;
        sb.append(")");
        sb.append(appendThrowsIfRequested(includingThrows));
        return sb.toString();
    }

    protected String appendThrowsIfRequested(boolean includingThrows) {
        StringBuilder sb = new StringBuilder();
        if (includingThrows) {
            boolean firstThrow = true;
            for (ReferenceType thr : getThrownExceptions()) {
                if (firstThrow) {
                    firstThrow = false;
                    sb.append(" throws ");
                } else {
                    sb.append(", ");
                }
                sb.append(thr.toString(prettyPrinterNoCommentsConfiguration));
            }
        }
        return sb.toString();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
            }
        }
        for (int i = 0; i < thrownExceptions.size(); i++) {
            if (thrownExceptions.get(i) == node) {
                thrownExceptions.remove(i);
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
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public CompactConstructorDeclaration clone() {
        return (CompactConstructorDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public CompactConstructorDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.compactConstructorDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == body) {
            setBody((BlockStmt) replacementNode);
            return true;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        for (int i = 0; i < thrownExceptions.size(); i++) {
            if (thrownExceptions.get(i) == node) {
                thrownExceptions.set(i, (ReferenceType) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < typeParameters.size(); i++) {
            if (typeParameters.get(i) == node) {
                typeParameters.set(i, (TypeParameter) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCompactConstructorDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public CompactConstructorDeclaration asCompactConstructorDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCompactConstructorDeclaration(Consumer<CompactConstructorDeclaration> action) {
        action.accept(this);
    }

    @Override
    public ResolvedConstructorDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedConstructorDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CompactConstructorDeclaration> toCompactConstructorDeclaration() {
        return Optional.of(this);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public CompactConstructorDeclaration(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, BlockStmt body) {
        super(tokenRange, annotations);
        setBody(body);
        customInitialization();
    }
}
