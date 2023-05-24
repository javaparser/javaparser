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
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.LocalRecordDeclarationStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.metamodel.RecordDeclarationMetaModel;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.Collections.unmodifiableList;
import static java.util.stream.Collectors.toList;

/**
 * <h1>The record declaration</h1>
 * <strong>WARNING: This implementation is subject to change.</strong>
 *
 * <h2>Java 1.0 to 13</h2>
 * Not available.
 * <br>
 * <h2>Java 14 (preview), Java 15 (2nd preview), Java 16</h2>
 * <p>
 * A definition of a record.<br>
 * {@code record X(...) { ... }}
 * </p><p>
 * Note that the syntax of records is substantively different to standard classes/interfaces/enums. Specifically, note
 * that record header contains the component declarations - where a "component" is defined as a non-static field.
 * </p><p>
 * This is in contrast to "normal" classes, where fields declarations are within the class body (optionally  then
 * initialised
 * within a constructor.
 * </p><p>
 * Also note that the constructor for records does not accept any parameters.
 * </p>
 *
 * <p>
 * Consider this example from https://openjdk.java.net/jeps/359
 * <pre>{@code
 *     record Range(int lo, int hi) {
 *         public Range {
 *             if (lo > hi)
 *                 throw new IllegalArgumentException(String.format("(%d,%d)",lo,hi));
 *         }
 *     }
 * }</pre>
 * </p><p>
 * To access these non-static field declarations, use {@link RecordDeclaration#getParameters()}
 * </p>
 *
 * @author Roger Howell
 * @see <a href="https://openjdk.java.net/jeps/359">https://openjdk.java.net/jeps/395</a>
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se16/html/jls-8.html#jls-8.10">JLS 8.10 - Record Classes</a>
 * @since 3.22.0
 */
public class RecordDeclaration extends TypeDeclaration<RecordDeclaration> implements NodeWithParameters<RecordDeclaration>, NodeWithImplements<RecordDeclaration>, NodeWithTypeParameters<RecordDeclaration>, NodeWithFinalModifier<RecordDeclaration>, Resolvable<ResolvedReferenceTypeDeclaration> {

    private NodeList<TypeParameter> typeParameters;

    private NodeList<ClassOrInterfaceType> implementedTypes;

    @OptionalProperty
    private ReceiverParameter receiverParameter;

    private NodeList<Parameter> parameters;

    public RecordDeclaration() {
        this(null, new NodeList<>(), new NodeList<>(), new SimpleName(), new NodeList<>(), new NodeList<>(), new NodeList<>(), new NodeList<>(), null);
    }

    public RecordDeclaration(final NodeList<Modifier> modifiers, final String name) {
        this(null, modifiers, new NodeList<>(), new SimpleName(name), new NodeList<>(), new NodeList<>(), new NodeList<>(), new NodeList<>(), null);
    }

    @AllFieldsConstructor
    public RecordDeclaration(final NodeList<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final SimpleName name, final NodeList<Parameter> parameters, final NodeList<TypeParameter> typeParameters, final NodeList<ClassOrInterfaceType> implementedTypes, final NodeList<BodyDeclaration<?>> members, final ReceiverParameter receiverParameter) {
        this(null, modifiers, annotations, name, parameters, typeParameters, implementedTypes, members, receiverParameter);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public RecordDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Parameter> parameters, NodeList<TypeParameter> typeParameters, NodeList<ClassOrInterfaceType> implementedTypes, NodeList<BodyDeclaration<?>> members, ReceiverParameter receiverParameter) {
        super(tokenRange, modifiers, annotations, name, members);
        setParameters(parameters);
        setTypeParameters(typeParameters);
        setImplementedTypes(implementedTypes);
        setReceiverParameter(receiverParameter);
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
    public NodeList<ClassOrInterfaceType> getImplementedTypes() {
        return implementedTypes;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordDeclaration setImplementedTypes(final NodeList<ClassOrInterfaceType> implementedTypes) {
        assertNotNull(implementedTypes);
        if (implementedTypes == this.implementedTypes) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.IMPLEMENTED_TYPES, this.implementedTypes, implementedTypes);
        if (this.implementedTypes != null)
            this.implementedTypes.setParentNode(null);
        this.implementedTypes = implementedTypes;
        setAsParentNodeOf(implementedTypes);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
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

    // TODO document and remove duplication between here and com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
    /**
     * @return is this class's parent a LocalRecordDeclarationStmt ?
     */
    public boolean isLocalRecordDeclaration() {
        return getParentNode().map(p -> p instanceof LocalRecordDeclarationStmt).orElse(false);
    }

    // TODO document and remove duplication between here and com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
    @Override
    public Optional<String> getFullyQualifiedName() {
        if (isLocalRecordDeclaration()) {
            return Optional.empty();
        }
        return super.getFullyQualifiedName();
    }

    @Override
    public ResolvedReferenceTypeDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedReferenceTypeDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isRecordDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public RecordDeclaration asRecordDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<RecordDeclaration> toRecordDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifRecordDeclaration(Consumer<RecordDeclaration> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.remove(i);
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
        for (int i = 0; i < typeParameters.size(); i++) {
            if (typeParameters.get(i) == node) {
                typeParameters.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.set(i, (ClassOrInterfaceType) replacementNode);
                return true;
            }
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
        for (int i = 0; i < typeParameters.size(); i++) {
            if (typeParameters.get(i) == node) {
                typeParameters.set(i, (TypeParameter) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public RecordDeclaration clone() {
        return (RecordDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public RecordDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.recordDeclarationMetaModel;
    }

    /**
     * Type declarations do not normally have parameters - e.g. {@code class X {}} and {@code enum X {}}.
     * Records are different, where the record declaration can include parameters e.g. {@code record X(int a) {}}.
     * Additionally, note that the constructor for a record does not allow the declaration of parameters.
     * See the JEP for details.
     *
     * @see <a href="https://openjdk.java.net/jeps/359">https://openjdk.java.net/jeps/359</a>
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordDeclaration setParameters(final NodeList<Parameter> parameters) {
        assertNotNull(parameters);
        if (parameters == this.parameters) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PARAMETERS, this.parameters, parameters);
        if (this.parameters != null)
            this.parameters.setParentNode(null);
        this.parameters = parameters;
        setAsParentNodeOf(parameters);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<ReceiverParameter> getReceiverParameter() {
        return Optional.ofNullable(receiverParameter);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordDeclaration setReceiverParameter(final ReceiverParameter receiverParameter) {
        if (receiverParameter == this.receiverParameter) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.RECEIVER_PARAMETER, this.receiverParameter, receiverParameter);
        if (this.receiverParameter != null)
            this.receiverParameter.setParentNode(null);
        this.receiverParameter = receiverParameter;
        setAsParentNodeOf(receiverParameter);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public RecordDeclaration removeReceiverParameter() {
        return setReceiverParameter((ReceiverParameter) null);
    }

    /**
     * Records are implicitly final, even without the explicit modifier.
     * https://openjdk.java.net/jeps/359#Restrictions-on-records
     *
     * If wanting to find out if the keyword {@code final} is explicitly added to this parameter,
     * you should use {@code node.hasModifier(Modifier.Keyword.FINAL)}
     *
     * @return always true -- Records are always implicitly final, therefore can never not be final.
     */
    @Override
    public boolean isFinal() {
        return true;
    }

    /**
     * Record components are implicitly static when nested (i.e. when the parent isn't a compilation unit).
     * https://openjdk.java.net/jeps/359#Restrictions-on-records
     *
     * @return True if the record declaration is nested, otherwise use the default method implementation.
     */
    @Override
    public boolean isStatic() {
        if (getParentNode().isPresent()) {
            Node parentNode = getParentNode().get();
            if (!(parentNode instanceof CompilationUnit)) {
                return true;
            }
        }
        // Otherwise use the default method.
        return super.isStatic();
    }

    /**
     * @return Only the "compact" constructors within this record,
     * not "normal" constructors (which are obtainable via {@link #getConstructors()}).
     */
    public List<CompactConstructorDeclaration> getCompactConstructors() {
        return unmodifiableList(getMembers().stream().filter(m -> m instanceof CompactConstructorDeclaration).map(m -> (CompactConstructorDeclaration) m).collect(toList()));
    }
}
