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
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class ConstructorDeclaration extends BodyDeclaration<ConstructorDeclaration>
        implements NodeWithJavaDoc<ConstructorDeclaration>, NodeWithDeclaration,
        NodeWithName<ConstructorDeclaration>, NodeWithModifiers<ConstructorDeclaration>,
        NodeWithParameters<ConstructorDeclaration>, NodeWithThrowable<ConstructorDeclaration>,
        NodeWithBlockStmt<ConstructorDeclaration> {

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private List<TypeParameter> typeParameterList;

    private NameExpr name;

    private List<Parameter> parametersList;

    private List<ReferenceType> throwsList;

    private BlockStmt body;

    public ConstructorDeclaration() {
    }

    public ConstructorDeclaration(EnumSet<Modifier> modifiers, String name) {
        setModifiers(modifiers);
        setName(name);
    }

    public ConstructorDeclaration(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations,
                                  List<TypeParameter> typeParameterList,
                                  String name, List<Parameter> parametersList, List<ReferenceType> throwsList,
                                  BlockStmt block) {
        super(annotations);
        setModifiers(modifiers);
        setTypeParameterList(typeParameterList);
        setName(name);
        setParametersList(parametersList);
        setThrowsList(throwsList);
        setBody(block);
    }

    public ConstructorDeclaration(Range range, EnumSet<Modifier> modifiers,
                                  List<AnnotationExpr> annotations, List<TypeParameter> typeParameterList, String name,
                                  List<Parameter> parametersList, List<ReferenceType> throwsList, BlockStmt block) {
        super(range, annotations);
        setModifiers(modifiers);
        setTypeParameterList(typeParameterList);
        setName(name);
        setParametersList(parametersList);
        setThrowsList(throwsList);
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
        return name == null ? null : name.getName();
    }

    public NameExpr getNameExpr() {
        return name;
    }

    @Override
    public List<Parameter> getParametersList() {
        parametersList = ensureNotNull(parametersList);
        return parametersList;
    }

    @Override
    public List<ReferenceType> getThrowsList() {
        throwsList = ensureNotNull(throwsList);
        return throwsList;
    }

    public List<TypeParameter> getTypeParameterList() {
        typeParameterList = ensureNotNull(typeParameterList);
        return typeParameterList;
    }

    @Override
    public ConstructorDeclaration setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public ConstructorDeclaration setName(String name) {
        setNameExpr(new NameExpr(name));
        return this;
    }

    public ConstructorDeclaration setNameExpr(NameExpr name) {
        this.name = name;
        setAsParentNodeOf(this.name);
        return this;
    }

    @Override
    public ConstructorDeclaration setParametersList(List<Parameter> parametersList) {
        this.parametersList = parametersList;
        setAsParentNodeOf(this.parametersList);
        return this;
    }

    @Override
    public ConstructorDeclaration setThrowsList(List<ReferenceType> throwsList) {
        this.throwsList = throwsList;
        setAsParentNodeOf(this.throwsList);
        return this;
    }

    public void setTypeParameterList(List<TypeParameter> typeParameterList) {
        this.typeParameterList = typeParameterList;
        setAsParentNodeOf(this.typeParameterList);
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
        for (Parameter param : getParametersList()) {
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
            for (ReferenceType thr : getThrowsList()) {
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
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }
}
