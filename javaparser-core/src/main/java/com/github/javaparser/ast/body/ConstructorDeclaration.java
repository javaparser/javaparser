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
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;

import static com.github.javaparser.ast.expr.NameExpr.name;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class ConstructorDeclaration extends BodyDeclaration<ConstructorDeclaration> implements 
        NodeWithJavaDoc<ConstructorDeclaration>, 
        NodeWithDeclaration,
        NodeWithName<ConstructorDeclaration>, 
        NodeWithModifiers<ConstructorDeclaration>,
        NodeWithParameters<ConstructorDeclaration>, 
        NodeWithThrowable<ConstructorDeclaration>,
        NodeWithBlockStmt<ConstructorDeclaration>,
        NodeWithTypeParameters<ConstructorDeclaration> {

    private EnumSet<Modifier> modifiers;

    private NodeList<TypeParameter> typeParameters;

    private NameExpr name;

    private NodeList<Parameter> parameters;

    private NodeList<ReferenceType<?>> throws_;

    private BlockStmt body;

    public ConstructorDeclaration() {
        this(Range.UNKNOWN,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new NodeList<>(),
                new NameExpr(),
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public ConstructorDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(Range.UNKNOWN,
                modifiers,
                new NodeList<>(),
                new NodeList<>(),
                name(name),
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public ConstructorDeclaration(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations,
                                  NodeList<TypeParameter> typeParameters,
                                  NameExpr name, NodeList<Parameter> parameters, NodeList<ReferenceType<?>> throws_,
                                  BlockStmt block) {
        this(Range.UNKNOWN,
                modifiers,
                annotations,
                typeParameters,
                name,
                parameters,
                throws_,
                block);
    }

    public ConstructorDeclaration(Range range, EnumSet<Modifier> modifiers,
                                  NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, NameExpr name,
                                  NodeList<Parameter> parameters, NodeList<ReferenceType<?>> throws_, BlockStmt block) {
        super(range, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setNameExpr(name);
        setParameters(parameters);
        setThrows(throws_);
        setBody(block);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
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
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    @Override
    public NodeList<ReferenceType<?>> getThrows() {
        return throws_;
    }

    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    @Override
    public ConstructorDeclaration setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = assertNotNull(modifiers);
        return this;
    }

    @Override
    public ConstructorDeclaration setName(String name) {
        setNameExpr(new NameExpr(assertNotNull(name)));
        return this;
    }

    public ConstructorDeclaration setNameExpr(NameExpr name) {
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }

    @Override
    public ConstructorDeclaration setParameters(NodeList<Parameter> parameters) {
        this.parameters = assertNotNull(parameters);
        setAsParentNodeOf(this.parameters);
        return this;
    }

    @Override
    public ConstructorDeclaration setThrows(NodeList<ReferenceType<?>> throws_) {
        this.throws_ = assertNotNull(throws_);
        setAsParentNodeOf(this.throws_);
        return this;
    }

    public ConstructorDeclaration setTypeParameters(NodeList<TypeParameter> typeParameters) {
        this.typeParameters = assertNotNull(typeParameters);
        setAsParentNodeOf(this.typeParameters);
        return this;
    }

    /**
     * The declaration returned has this schema:
     *
     * [accessSpecifier] className ([paramType [paramName]])
     * [throws exceptionsList]
     */
    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows,
                                         boolean includingParameterName) {
        StringBuilder sb = new StringBuilder();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = Modifier.getAccessSpecifier(getModifiers());
            sb.append(accessSpecifier.getCodeRepresenation());
            sb.append(accessSpecifier == AccessSpecifier.DEFAULT ? "" : " ");
        }
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
                sb.append(thr.toString(prettyPrinterNoCommentsConfiguration));
            }
        }
        return sb.toString();
    }

    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows) {
        return getDeclarationAsString(includingModifiers, includingThrows, true);
    }

    @Override
    public String getDeclarationAsString() {
        return getDeclarationAsString(true, true, true);
    }

    @Override
    public JavadocComment getJavaDoc() {
        if (getComment() instanceof JavadocComment) {
            return (JavadocComment) getComment();
        }
        return null;
    }

    @Override
    public BlockStmt getBody() {
        return body;
    }

    @Override
    public ConstructorDeclaration setBody(BlockStmt body) {
        this.body = assertNotNull(body);
        setAsParentNodeOf(body);
        return this;
    }
}
