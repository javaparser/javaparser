/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import java.util.List;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.NamedNode;
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.ast.internal.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class ConstructorDeclaration extends BodyDeclaration implements DocumentableNode, WithDeclaration,
        NamedNode {

    private int modifiers;

    private List<TypeParameter> typeParameters;

    private NameExpr name;

    private List<Parameter> parameters;

    private List<NameExpr> throws_;

    private BlockStmt block;

    public ConstructorDeclaration() {
    }

    public ConstructorDeclaration(int modifiers, String name) {
        setModifiers(modifiers);
        setName(name);
    }

    public ConstructorDeclaration(int modifiers, List<AnnotationExpr> annotations, List<TypeParameter> typeParameters,
                                  String name, List<Parameter> parameters, List<NameExpr> throws_, BlockStmt block) {
        super(annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setName(name);
        setParameters(parameters);
        setThrows(throws_);
        setBlock(block);
    }

    public ConstructorDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers,
                                  List<AnnotationExpr> annotations, List<TypeParameter> typeParameters, String name,
                                  List<Parameter> parameters, List<NameExpr> throws_, BlockStmt block) {
        super(beginLine, beginColumn, endLine, endColumn, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setName(name);
        setParameters(parameters);
        setThrows(throws_);
        setBlock(block);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public BlockStmt getBlock() {
        return block;
    }

    /**
     * Return the modifiers of this member declaration.
     * 
     * @see ModifierSet
     * @return modifiers
     */
    public int getModifiers() {
        return modifiers;
    }

    @Override
    public String getName() {
        return name == null ? null : name.getName();
    }

    public NameExpr getNameExpr() {
        return name;
    }

    public List<Parameter> getParameters() {
        parameters = ensureNotNull(parameters);
        return parameters;
    }

    public List<NameExpr> getThrows() {
        throws_ = ensureNotNull(throws_);
        return throws_;
    }

    public List<TypeParameter> getTypeParameters() {
        typeParameters = ensureNotNull(typeParameters);
        return typeParameters;
    }

    public void setBlock(BlockStmt block) {
        this.block = block;
        setAsParentNodeOf(this.block);
    }

    public void setModifiers(int modifiers) {
        this.modifiers = modifiers;
    }

    public void setName(String name) {
        this.name = new NameExpr(name);
    }

    public void setNameExpr(NameExpr name) {
        this.name = name;
    }

    public void setParameters(List<Parameter> parameters) {
        this.parameters = parameters;
        setAsParentNodeOf(this.parameters);
    }

    public void setThrows(List<NameExpr> throws_) {
        this.throws_ = throws_;
        setAsParentNodeOf(this.throws_);
    }

    public void setTypeParameters(List<TypeParameter> typeParameters) {
        this.typeParameters = typeParameters;
		setAsParentNodeOf(this.typeParameters);
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
        StringBuffer sb = new StringBuffer();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = ModifierSet.getAccessSpecifier(getModifiers());
            sb.append(accessSpecifier.getCodeRepresenation());
            sb.append(accessSpecifier == AccessSpecifier.DEFAULT ? "" : " ");
        }
        sb.append(getName());
        sb.append("(");
        boolean firstParam = true;
        for (Parameter param : getParameters())
        {
            if (firstParam) {
                firstParam = false;
            } else {
                sb.append(", ");
            }
            if (includingParameterName) {
                sb.append(param.toStringWithoutComments());
            } else {
                sb.append(param.getType().toStringWithoutComments());
            }
        }
        sb.append(")");
        if (includingThrows) {
            boolean firstThrow = true;
            for (NameExpr thr : getThrows()) {
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
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows) {
        return getDeclarationAsString(includingModifiers, includingThrows, true);
    }

    @Override
    public String getDeclarationAsString() {
        return getDeclarationAsString(true, true, true);
    }

    @Override
    public void setJavaDoc(JavadocComment javadocComment) {
        this.javadocComment = javadocComment;
    }

    @Override
    public JavadocComment getJavaDoc() {
        return javadocComment;
    }

    private JavadocComment javadocComment;
}
