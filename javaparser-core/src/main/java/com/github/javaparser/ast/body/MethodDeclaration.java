/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.nodeTypes.modifiers.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.EnumSet;
import java.util.Optional;
import static com.github.javaparser.ast.Modifier.*;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.MethodDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import java.util.function.Consumer;

/**
 * A method declaration. "public int abc() {return 1;}" in this example: <code>class X { public int abc() {return 1;}
 * }</code>
 *
 * <br/>All annotations preceding the return type will be set on this object, not on the return type.
 * JavaParser doesn't know if it they are applicable to the method or the type.
 *
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends CallableDeclaration<MethodDeclaration> implements NodeWithType<MethodDeclaration, Type>, NodeWithOptionalBlockStmt<MethodDeclaration>, NodeWithJavadoc<MethodDeclaration>, NodeWithDeclaration, NodeWithSimpleName<MethodDeclaration>, NodeWithParameters<MethodDeclaration>, NodeWithThrownExceptions<MethodDeclaration>, NodeWithTypeParameters<MethodDeclaration>, NodeWithAccessModifiers<MethodDeclaration>, NodeWithAbstractModifier<MethodDeclaration>, NodeWithStaticModifier<MethodDeclaration>, NodeWithFinalModifier<MethodDeclaration>, NodeWithStrictfpModifier<MethodDeclaration>, Resolvable<ResolvedMethodDeclaration> {

    private Type type;

    @OptionalProperty
    private BlockStmt body;

    public MethodDeclaration() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), new NodeList<>(), new ClassOrInterfaceType(), new SimpleName(), new NodeList<>(), new NodeList<>(), new BlockStmt(), null);
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type type, final String name) {
        this(null, modifiers, new NodeList<>(), new NodeList<>(), type, new SimpleName(name), new NodeList<>(), new NodeList<>(), new BlockStmt(), null);
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final String name, final Type type, final NodeList<Parameter> parameters) {
        this(null, modifiers, new NodeList<>(), new NodeList<>(), type, new SimpleName(name), parameters, new NodeList<>(), new BlockStmt(), null);
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<TypeParameter> typeParameters, final Type type, final SimpleName name, final NodeList<Parameter> parameters, final NodeList<ReferenceType> thrownExceptions, final BlockStmt body) {
        this(null, modifiers, annotations, typeParameters, type, name, parameters, thrownExceptions, body, null);
    }

    @AllFieldsConstructor
    public MethodDeclaration(final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<TypeParameter> typeParameters, final Type type, final SimpleName name, final NodeList<Parameter> parameters, final NodeList<ReferenceType> thrownExceptions, final BlockStmt body, ReceiverParameter receiverParameter) {
        this(null, modifiers, annotations, typeParameters, type, name, parameters, thrownExceptions, body, receiverParameter);
    }

    /**
     * @deprecated this constructor allows you to set "isDefault", but this is no longer a field of this node, but simply one of the modifiers. Use setDefault(boolean) or add DEFAULT to the modifiers set.
     */
    @Deprecated
    public MethodDeclaration(final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<TypeParameter> typeParameters, final Type type, final SimpleName name, final boolean isDefault, final NodeList<Parameter> parameters, final NodeList<ReferenceType> thrownExceptions, final BlockStmt body) {
        this(null, modifiers, annotations, typeParameters, type, name, parameters, thrownExceptions, body, null);
        setDefault(isDefault);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public MethodDeclaration(TokenRange tokenRange, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, Type type, SimpleName name, NodeList<Parameter> parameters, NodeList<ReferenceType> thrownExceptions, BlockStmt body, ReceiverParameter receiverParameter) {
        super(tokenRange, modifiers, annotations, typeParameters, name, parameters, thrownExceptions, receiverParameter);
        setType(type);
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
    public Optional<BlockStmt> getBody() {
        return Optional.ofNullable(body);
    }

    /**
     * Sets the body
     *
     * @param body the body, can be null
     * @return this, the MethodDeclaration
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public MethodDeclaration setBody(final BlockStmt body) {
        if (body == this.body) {
            return (MethodDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public MethodDeclaration setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return (MethodDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    public MethodDeclaration setModifiers(final EnumSet<Modifier> modifiers) {
        return super.setModifiers(modifiers);
    }

    @Override
    public MethodDeclaration setName(final SimpleName name) {
        return super.setName(name);
    }

    @Override
    public MethodDeclaration setParameters(final NodeList<Parameter> parameters) {
        return super.setParameters(parameters);
    }

    @Override
    public MethodDeclaration setThrownExceptions(final NodeList<ReferenceType> thrownExceptions) {
        return super.setThrownExceptions(thrownExceptions);
    }

    @Override
    public MethodDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        return super.setTypeParameters(typeParameters);
    }

    /**
     * The declaration returned has this schema:
     * <p>
     * [accessSpecifier] [static] [abstract] [final] [native]
     * [synchronized] returnType methodName ([paramType [paramName]])
     * [throws exceptionsList]
     *
     * @return method declaration as String
     */
    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows, boolean includingParameterName) {
        StringBuilder sb = new StringBuilder();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = getAccessSpecifier(getModifiers());
            sb.append(accessSpecifier.asString());
            sb.append(accessSpecifier == AccessSpecifier.DEFAULT ? "" : " ");
            if (getModifiers().contains(STATIC)) {
                sb.append("static ");
            }
            if (getModifiers().contains(ABSTRACT)) {
                sb.append("abstract ");
            }
            if (getModifiers().contains(FINAL)) {
                sb.append("final ");
            }
            if (getModifiers().contains(NATIVE)) {
                sb.append("native ");
            }
            if (getModifiers().contains(SYNCHRONIZED)) {
                sb.append("synchronized ");
            }
        }
        sb.append(getType().toString(prettyPrinterNoCommentsConfiguration));
        sb.append(" ");
        sb.append(getName());
        sb.append("(");
        boolean firstParam = true;
        for (Parameter param : getParameters()) {
            if (firstParam) {
                firstParam = false;
            } else {
                sb.append(", ");
            }
            if (includingParameterName) {
                sb.append(param.toString(prettyPrinterNoCommentsConfiguration));
            } else {
                sb.append(param.getType().toString(prettyPrinterNoCommentsConfiguration));
                if (param.isVarArgs()) {
                    sb.append("...");
                }
            }
        }
        sb.append(")");
        sb.append(appendThrowsIfRequested(includingThrows));
        return sb.toString();
    }

    public boolean isNative() {
        return getModifiers().contains(NATIVE);
    }

    public boolean isSynchronized() {
        return getModifiers().contains(SYNCHRONIZED);
    }

    public boolean isDefault() {
        return getModifiers().contains(DEFAULT);
    }

    public MethodDeclaration setNative(boolean set) {
        return setModifier(NATIVE, set);
    }

    public MethodDeclaration setSynchronized(boolean set) {
        return setModifier(SYNCHRONIZED, set);
    }

    public MethodDeclaration setDefault(boolean set) {
        return setModifier(DEFAULT, set);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (body != null) {
            if (node == body) {
                removeBody();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public MethodDeclaration removeBody() {
        return setBody((BlockStmt) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public MethodDeclaration clone() {
        return (MethodDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public MethodDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.methodDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (body != null) {
            if (node == body) {
                setBody((BlockStmt) replacementNode);
                return true;
            }
        }
        if (node == type) {
            setType((Type) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodDeclaration asMethodDeclaration() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodDeclaration(Consumer<MethodDeclaration> action) {
        action.accept(this);
    }

    @Override
    public ResolvedMethodDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedMethodDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MethodDeclaration> toMethodDeclaration() {
        return Optional.of(this);
    }
}
