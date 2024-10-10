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

import static com.github.javaparser.ast.type.ArrayType.*;
import static com.github.javaparser.ast.type.ArrayType.wrapInArrayTypes;
import static com.github.javaparser.utils.Utils.ensureNotNull;

import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Pair;

import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends BodyDeclaration<MethodDeclaration> implements 
        NodeWithJavaDoc<MethodDeclaration>, 
        NodeWithDeclaration, 
        NodeWithName<MethodDeclaration>,
        NodeWithType<MethodDeclaration>,
        NodeWithElementType<MethodDeclaration>,
        NodeWithModifiers<MethodDeclaration>, 
        NodeWithParameters<MethodDeclaration>,
        NodeWithThrowable<MethodDeclaration>, 
        NodeWithBlockStmt<MethodDeclaration> {

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private List<TypeParameter> typeParameters;

    private Type elementType;

    private NameExpr name;

    private List<Parameter> parameters;

    private List<ReferenceType> throws_;

    private BlockStmt body;

    private boolean isDefault = false;

    private List<ArrayBracketPair> arrayBracketPairsAfterType;

    private List<ArrayBracketPair> arrayBracketPairsAfterParameterList;

    public MethodDeclaration() {
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type elementType, final String name) {
        setModifiers(modifiers);
        setElementType(elementType);
        setName(name);
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type elementType, final String name,
                             final List<Parameter> parameters) {
        setModifiers(modifiers);
        setElementType(elementType);
        setName(name);
        setParameters(parameters);
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, 
                             final List<AnnotationExpr> annotations,
                             final List<TypeParameter> typeParameters, 
                             final Type elementType,
                             final List<ArrayBracketPair> arrayBracketPairsAfterElementType,
                             final String name,
                             final List<Parameter> parameters, 
                             final List<ArrayBracketPair> arrayBracketPairsAfterParameterList,
                             final List<ReferenceType> throws_, 
                             final BlockStmt body) {
        super(annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setElementType(elementType);
        setName(name);
        setParameters(parameters);
        setArrayBracketPairsAfterElementType(arrayBracketPairsAfterElementType);
        setArrayBracketPairsAfterParameterList(arrayBracketPairsAfterParameterList);
        setThrows(throws_);
        setBody(body);
    }

    public MethodDeclaration(Range range,
                             final EnumSet<Modifier> modifiers, 
                             final List<AnnotationExpr> annotations,
                             final List<TypeParameter> typeParameters, 
                             final Type elementType,
                             final List<ArrayBracketPair> arrayBracketPairsAfterElementType,
                             final NameExpr nameExpr,
                             final List<Parameter> parameters, 
                             final List<ArrayBracketPair> arrayBracketPairsAfterParameterList,
                             final List<ReferenceType> throws_, 
                             final BlockStmt body) {
        super(range, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setElementType(elementType);
        setNameExpr(nameExpr);
        setParameters(parameters);
        setArrayBracketPairsAfterElementType(arrayBracketPairsAfterElementType);
        setArrayBracketPairsAfterParameterList(arrayBracketPairsAfterParameterList);
        setThrows(throws_);
        setBody(body);
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
    public BlockStmt getBody() {
        return body;
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
    public String getName() {
        return name.getName();
    }

    public NameExpr getNameExpr() {
        return name;
    }

    @Override
    public List<Parameter> getParameters() {
        parameters = ensureNotNull(parameters);
        return parameters;
    }

    @Override
    public List<ReferenceType> getThrows() {
        throws_ = ensureNotNull(throws_);
        return throws_;
    }

    @Override
    public Type getType() {
        return wrapInArrayTypes(getElementType(),
                getArrayBracketPairsAfterElementType(),
                getArrayBracketPairsAfterParameterList());
    }

    @Override
    public Type getElementType() {
        return elementType;
    }

    public List<TypeParameter> getTypeParameters() {
        typeParameters = ensureNotNull(typeParameters);
        return typeParameters;
    }

    @Override
    public MethodDeclaration setBody(final BlockStmt body) {
        this.body = body;
        setAsParentNodeOf(this.body);
        return this;
    }

    @Override
    public MethodDeclaration setModifiers(final EnumSet<Modifier> modifiers) {
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public MethodDeclaration setName(final String name) {
        setNameExpr(new NameExpr(name));
        return this;
    }

    public MethodDeclaration setNameExpr(final NameExpr name) {
        this.name = name;
        setAsParentNodeOf(this.name);
        return this;
    }

    @Override
    public MethodDeclaration setParameters(final List<Parameter> parameters) {
        this.parameters = parameters;
        setAsParentNodeOf(this.parameters);
        return this;
    }

    @Override
    public MethodDeclaration setThrows(final List<ReferenceType> throws_) {
        this.throws_ = throws_;
        setAsParentNodeOf(this.throws_);
        return this;
    }

    @Override
    public MethodDeclaration setType(final Type type) {
        Pair<Type, List<ArrayBracketPair>> typeListPair = unwrapArrayTypes(type);
        setElementType(typeListPair.a);
        setArrayBracketPairsAfterElementType(typeListPair.b);
        setArrayBracketPairsAfterParameterList(null);
        return this;
    }

    @Override
    public MethodDeclaration setElementType(final Type elementType) {
        this.elementType = elementType;
        setAsParentNodeOf(this.elementType);
        return this;
    }

    public MethodDeclaration setTypeParameters(final List<TypeParameter> typeParameters) {
        this.typeParameters = typeParameters;
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
        sb.append(getElementType().toStringWithoutComments());
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
                sb.append(param.toStringWithoutComments());
            } else {
                sb.append(param.getElementType().toStringWithoutComments());
                if (param.isVarArgs()) {
                    sb.append("...");
                }
            }
        }
        sb.append(")");
        if (includingThrows) {
            boolean firstThrow = true;
            for (ReferenceType thr : getThrows()) {
                if (firstThrow) {
                    firstThrow = false;
                    sb.append(" throws ");
                } else {
                    sb.append(", ");
                }
                sb.append(thr.toStringWithoutComments());
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
    public List<ArrayBracketPair> getArrayBracketPairsAfterElementType() {
        arrayBracketPairsAfterType = ensureNotNull(arrayBracketPairsAfterType);
        return arrayBracketPairsAfterType;
    }

    @Override
    public MethodDeclaration setArrayBracketPairsAfterElementType(List<ArrayBracketPair> arrayBracketPairsAfterType) {
        this.arrayBracketPairsAfterType = arrayBracketPairsAfterType;
        setAsParentNodeOf(arrayBracketPairsAfterType);
        return this;
    }

	/**
     * @return the array brackets in this position: <code>int abc()[] {...}</code>
     */
    public List<ArrayBracketPair> getArrayBracketPairsAfterParameterList() {
        arrayBracketPairsAfterParameterList = ensureNotNull(arrayBracketPairsAfterParameterList);
        return arrayBracketPairsAfterParameterList;
    }

    public MethodDeclaration setArrayBracketPairsAfterParameterList(List<ArrayBracketPair> arrayBracketPairsAfterParameterList) {
        this.arrayBracketPairsAfterParameterList = arrayBracketPairsAfterParameterList;
        setAsParentNodeOf(arrayBracketPairsAfterParameterList);
        return this;
    }
}
