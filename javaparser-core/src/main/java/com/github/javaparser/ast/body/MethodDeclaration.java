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

import static com.github.javaparser.ast.type.ArrayType.unwrapArrayTypes;
import static com.github.javaparser.ast.type.ArrayType.wrapInArrayTypes;
import static com.github.javaparser.utils.Utils.assertNotNull;

import java.util.EnumSet;
import java.util.Optional;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithElementType;
import com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalBlockStmt;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithThrowable;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Pair;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends BodyDeclaration<MethodDeclaration> implements 
        NodeWithJavaDoc<MethodDeclaration>, 
        NodeWithDeclaration,
        NodeWithSimpleName<MethodDeclaration>,
        NodeWithType<MethodDeclaration, Type<?>>,
        NodeWithElementType<MethodDeclaration>,
        NodeWithModifiers<MethodDeclaration>, 
        NodeWithParameters<MethodDeclaration>,
        NodeWithThrowable<MethodDeclaration>, 
        NodeWithOptionalBlockStmt<MethodDeclaration>,
        NodeWithTypeParameters<MethodDeclaration> {

    private EnumSet<Modifier> modifiers;

    private NodeList<TypeParameter> typeParameters;

    private Type<?> elementType;

    private SimpleName name;

    private NodeList<Parameter> parameters;

    private NodeList<ReferenceType<?>> throws_;

    private BlockStmt body;

    private boolean isDefault;

    private NodeList<ArrayBracketPair> arrayBracketPairsAfterType;

    private NodeList<ArrayBracketPair> arrayBracketPairsAfterParameterList;

    public MethodDeclaration() {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new NodeList<>(),
                new ClassOrInterfaceType(),
                new NodeList<>(),
                new SimpleName(),
                false,
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type<?> elementType, final String name) {
        this(null,
                modifiers,
                new NodeList<>(),
                new NodeList<>(),
                elementType,
                new NodeList<>(),
                new SimpleName(name),
                false,
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type<?> elementType, final String name,
                             final NodeList<Parameter> parameters) {
        this(null,
                modifiers,
                new NodeList<>(),
                new NodeList<>(),
                elementType,
                new NodeList<>(),
                new SimpleName(name),
                false,
                parameters,
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, 
                             final NodeList<AnnotationExpr> annotations,
                             final NodeList<TypeParameter> typeParameters, 
                             final Type<?> elementType,
                             final NodeList<ArrayBracketPair> arrayBracketPairsAfterElementType,
                             final SimpleName name,
                             final boolean isDefault,
                             final NodeList<Parameter> parameters, 
                             final NodeList<ArrayBracketPair> arrayBracketPairsAfterParameterList,
                             final NodeList<ReferenceType<?>> throws_, 
                             final BlockStmt body) {
        this(null,
                modifiers,
                annotations,
                typeParameters,
                elementType,
                arrayBracketPairsAfterElementType,
                name,
                isDefault,
                parameters,
                arrayBracketPairsAfterParameterList,
                throws_,
                body);
    }

    public MethodDeclaration(Range range,
                             final EnumSet<Modifier> modifiers, 
                             final NodeList<AnnotationExpr> annotations,
                             final NodeList<TypeParameter> typeParameters, 
                             final Type<?> elementType,
                             final NodeList<ArrayBracketPair> arrayBracketPairsAfterElementType,
                             final SimpleName name,
                             final boolean isDefault,
                             final NodeList<Parameter> parameters, 
                             final NodeList<ArrayBracketPair> arrayBracketPairsAfterParameterList,
                             final NodeList<ReferenceType<?>> throws_, 
                             final BlockStmt body) {
        super(range, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setElementType(elementType);
        setName(name);
        setParameters(parameters);
        setArrayBracketPairsAfterElementType(arrayBracketPairsAfterElementType);
        setArrayBracketPairsAfterParameterList(arrayBracketPairsAfterParameterList);
        setThrows(throws_);
        setBody(body);
        setDefault(isDefault);
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
    public Optional<BlockStmt> getBody() {
        return Optional.ofNullable(body);
    }

    /**
     * Return the modifiers of this member declaration.
     * 
     * @see Modifier
     * @return modifiers
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    @Override
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    @Override
    public NodeList<ReferenceType<?>> getThrows() {
        return throws_;
    }

    @Override
    public Type<?> getType() {
        return wrapInArrayTypes(getElementType(),
                getArrayBracketPairsAfterElementType(),
                getArrayBracketPairsAfterParameterList());
    }

    @Override
    public Type<?> getElementType() {
        return elementType;
    }

    @Override
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    /**
     * Sets the body
     * 
     * @param body the body, can be null
     * @return this, the MethodDeclaration
     */
    @Override
    public MethodDeclaration setBody(final BlockStmt body) {
        this.body = body;
        setAsParentNodeOf(this.body);
        return this;
    }

    @Override
    public MethodDeclaration setModifiers(final EnumSet<Modifier> modifiers) {
        this.modifiers = assertNotNull(modifiers);
        return this;
    }

    @Override
    public MethodDeclaration setName(final SimpleName name) {
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }

    @Override
    public MethodDeclaration setParameters(final NodeList<Parameter> parameters) {
        this.parameters = assertNotNull(parameters);
        setAsParentNodeOf(this.parameters);
        return this;
    }

    @Override
    public MethodDeclaration setThrows(final NodeList<ReferenceType<?>> throws_) {
        this.throws_ = assertNotNull(throws_);
        setAsParentNodeOf(this.throws_);
        return this;
    }

    @Override
    public MethodDeclaration setType(final Type<?> type) {
        Pair<Type<?>, NodeList<ArrayBracketPair>> typeListPair = unwrapArrayTypes(assertNotNull(type));
        setElementType(typeListPair.a);
        setArrayBracketPairsAfterElementType(typeListPair.b);
        setArrayBracketPairsAfterParameterList(new NodeList<>());
        return this;
    }

    @Override
    public MethodDeclaration setElementType(final Type<?> elementType) {
        this.elementType = assertNotNull(elementType);
        setAsParentNodeOf(this.elementType);
        return this;
    }

    @Override
    public MethodDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        this.typeParameters = assertNotNull(typeParameters);
        setAsParentNodeOf(typeParameters);
        return this;
    }

    public boolean isDefault() {
        return isDefault;
    }

    public MethodDeclaration setDefault(boolean isDefault) {
        this.isDefault = isDefault;
        return this;
    }

    @Override
    public String getDeclarationAsString() {
        return getDeclarationAsString(true, true, true);
    }

    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows) {
        return getDeclarationAsString(includingModifiers, includingThrows, true);
    }

    /**
     * The declaration returned has this schema:
     *
     * [accessSpecifier] [static] [abstract] [final] [native]
     * [synchronized] returnType methodName ([paramType [paramName]])
     * [throws exceptionsList]
     * 
     * @return method declaration as String
     */
    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows,
                                         boolean includingParameterName) {
        StringBuilder sb = new StringBuilder();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = Modifier.getAccessSpecifier(getModifiers());
            sb.append(accessSpecifier.getCodeRepresenation());
            sb.append(accessSpecifier == AccessSpecifier.DEFAULT ? "" : " ");
            if (getModifiers().contains(Modifier.STATIC)) {
                sb.append("static ");
            }
            if (getModifiers().contains(Modifier.ABSTRACT)) {
                sb.append("abstract ");
            }
            if (getModifiers().contains(Modifier.FINAL)) {
                sb.append("final ");
            }
            if (getModifiers().contains(Modifier.NATIVE)) {
                sb.append("native ");
            }
            if (getModifiers().contains(Modifier.SYNCHRONIZED)) {
                sb.append("synchronized ");
            }
        }
        // TODO verify it does not print comments connected to the type
        sb.append(getElementType().toString(prettyPrinterNoCommentsConfiguration));
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
                sb.append(param.getElementType().toString(prettyPrinterNoCommentsConfiguration));
                if (param.isVarArgs()) {
                    sb.append("...");
                }
            }
        }
        sb.append(")");
        if (includingThrows) {
            boolean firstThrow = true;
            for (ReferenceType<?> thr : getThrows()) {
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
    public JavadocComment getJavaDoc() {
        if (getComment() instanceof JavadocComment) {
            return (JavadocComment) getComment();
        }
        return null;
    }

    /**
     * @return the array brackets in this position: <code>class C { int[] abc; }</code>
     */
    @Override
    public NodeList<ArrayBracketPair> getArrayBracketPairsAfterElementType() {
        return arrayBracketPairsAfterType;
    }

    @Override
    public MethodDeclaration setArrayBracketPairsAfterElementType(NodeList<ArrayBracketPair> arrayBracketPairsAfterType) {
        this.arrayBracketPairsAfterType = assertNotNull(arrayBracketPairsAfterType);
        setAsParentNodeOf(arrayBracketPairsAfterType);
        return this;
    }

	/**
     * @return the array brackets in this position: <code>int abc()[] {...}</code>
     */
    public NodeList<ArrayBracketPair> getArrayBracketPairsAfterParameterList() {
        return arrayBracketPairsAfterParameterList;
    }

    public MethodDeclaration setArrayBracketPairsAfterParameterList(NodeList<ArrayBracketPair> arrayBracketPairsAfterParameterList) {
        this.arrayBracketPairsAfterParameterList = assertNotNull(arrayBracketPairsAfterParameterList);
        setAsParentNodeOf(arrayBracketPairsAfterParameterList);
        return this;
    }
}
