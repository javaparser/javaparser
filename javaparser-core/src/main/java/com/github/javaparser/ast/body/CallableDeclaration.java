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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.nodeTypes.modifiers.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.CallableDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.ast.Generated;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toList;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Represents a declaration which is callable eg. a method or a constructor.
 */
public abstract class CallableDeclaration<T extends CallableDeclaration<?>> extends BodyDeclaration<T> implements NodeWithAccessModifiers<T>, NodeWithDeclaration, NodeWithSimpleName<T>, NodeWithParameters<T>, NodeWithThrownExceptions<T>, NodeWithTypeParameters<T>, NodeWithJavadoc<T>, NodeWithAbstractModifier<T>, NodeWithStaticModifier<T>, NodeWithFinalModifier<T>, NodeWithStrictfpModifier<T> {

    private NodeList<Modifier> modifiers;

    private NodeList<TypeParameter> typeParameters;

    private SimpleName name;

    private NodeList<Parameter> parameters;

    private NodeList<ReferenceType> thrownExceptions;

    @OptionalProperty
    private ReceiverParameter receiverParameter;

    @AllFieldsConstructor
    CallableDeclaration(NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, SimpleName name, NodeList<Parameter> parameters, NodeList<ReferenceType> thrownExceptions, ReceiverParameter receiverParameter) {
        this(null, modifiers, annotations, typeParameters, name, parameters, thrownExceptions, receiverParameter);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public CallableDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, SimpleName name, NodeList<Parameter> parameters, NodeList<ReferenceType> thrownExceptions, ReceiverParameter receiverParameter) {
        super(tokenRange, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setName(name);
        setParameters(parameters);
        setThrownExceptions(thrownExceptions);
        setReceiverParameter(receiverParameter);
        customInitialization();
    }

    /**
     * Return the modifiers of this member declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return (T) this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return (T) this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setParameters(final NodeList<Parameter> parameters) {
        assertNotNull(parameters);
        if (parameters == this.parameters) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.PARAMETERS, this.parameters, parameters);
        if (this.parameters != null)
            this.parameters.setParentNode(null);
        this.parameters = parameters;
        setAsParentNodeOf(parameters);
        return (T) this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ReferenceType> getThrownExceptions() {
        return thrownExceptions;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setThrownExceptions(final NodeList<ReferenceType> thrownExceptions) {
        assertNotNull(thrownExceptions);
        if (thrownExceptions == this.thrownExceptions) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.THROWN_EXCEPTIONS, this.thrownExceptions, thrownExceptions);
        if (this.thrownExceptions != null)
            this.thrownExceptions.setParentNode(null);
        this.thrownExceptions = thrownExceptions;
        setAsParentNodeOf(thrownExceptions);
        return (T) this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        assertNotNull(typeParameters);
        if (typeParameters == this.typeParameters) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        if (this.typeParameters != null)
            this.typeParameters.setParentNode(null);
        this.typeParameters = typeParameters;
        setAsParentNodeOf(typeParameters);
        return (T) this;
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
        if (node == null)
            return false;
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
            }
        }
        for (int i = 0; i < parameters.size(); i++) {
            if (parameters.get(i) == node) {
                parameters.remove(i);
                return true;
            }
        }
        if (receiverParameter != null) {
            if (node == receiverParameter) {
                removeReceiverParameter();
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

    /**
     * A method or constructor signature.
     * <p/>Note that since JavaParser has no real knowledge of types - only the text found in the source file - using
     * this will fail in some cases. (java.util.String != String for example, and generics are not taken into account.)
     */
    public static class Signature {

        private final String name;

        private final List<Type> parameterTypes;

        private Signature(String name, List<Type> parameterTypes) {
            this.name = name;
            this.parameterTypes = parameterTypes;
        }

        public String getName() {
            return name;
        }

        public List<Type> getParameterTypes() {
            return parameterTypes;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (o == null || getClass() != o.getClass())
                return false;
            Signature signature = (Signature) o;
            if (!name.equals(signature.name))
                return false;
            if (!parameterTypes.equals(signature.parameterTypes))
                return false;
            return true;
        }

        @Override
        public int hashCode() {
            int result = name.hashCode();
            result = 31 * result + parameterTypes.hashCode();
            return result;
        }

        public String asString() {
            return parameterTypes.stream().map(Type::asString).collect(joining(", ", name + "(", ")"));
        }

        @Override
        public String toString() {
            return asString();
        }
    }

    public Signature getSignature() {
        return new Signature(getName().getIdentifier(), getParameters().stream().map(this::getTypeWithVarargsAsArray).map(this::stripGenerics).map(this::stripAnnotations).collect(toList()));
    }

    private Type stripAnnotations(Type type) {
        if (type instanceof NodeWithAnnotations) {
            ((NodeWithAnnotations) type).setAnnotations(new NodeList<>());
        }
        return type;
    }

    private Type stripGenerics(Type type) {
        if (type instanceof NodeWithTypeArguments) {
            ((NodeWithTypeArguments) type).setTypeArguments((NodeList<Type>) null);
        }
        return type;
    }

    private Type getTypeWithVarargsAsArray(Parameter p) {
        /* A signature includes the varargs ellipsis.
         This is a field on parameter which we lose when we only get the type,
         so we represent it as an additional [] on the type. */
        Type t = p.getType().clone();
        if (p.isVarArgs()) {
            t = new ArrayType(t);
        }
        return t;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public CallableDeclaration<?> clone() {
        return (CallableDeclaration<?>) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public CallableDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.callableDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
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
        for (int i = 0; i < parameters.size(); i++) {
            if (parameters.get(i) == node) {
                parameters.set(i, (Parameter) replacementNode);
                return true;
            }
        }
        if (receiverParameter != null) {
            if (node == receiverParameter) {
                setReceiverParameter((ReceiverParameter) replacementNode);
                return true;
            }
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
    public boolean isCallableDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public CallableDeclaration asCallableDeclaration() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCallableDeclaration(Consumer<CallableDeclaration> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<ReceiverParameter> getReceiverParameter() {
        return Optional.ofNullable(receiverParameter);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setReceiverParameter(final ReceiverParameter receiverParameter) {
        if (receiverParameter == this.receiverParameter) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.RECEIVER_PARAMETER, this.receiverParameter, receiverParameter);
        if (this.receiverParameter != null)
            this.receiverParameter.setParentNode(null);
        this.receiverParameter = receiverParameter;
        setAsParentNodeOf(receiverParameter);
        return (T) this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public CallableDeclaration removeReceiverParameter() {
        return setReceiverParameter((ReceiverParameter) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CallableDeclaration> toCallableDeclaration() {
        return Optional.of(this);
    }
}
