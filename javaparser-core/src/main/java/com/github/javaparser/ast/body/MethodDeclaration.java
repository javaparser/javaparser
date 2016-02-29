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

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.ast.internal.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends BodyDeclaration implements DocumentableNode, WithDeclaration, NamedNode, TypedNode {

	private int modifiers;

	private List<TypeParameter> typeParameters;

	private Type type;

	private NameExpr name;

	private List<Parameter> parameters;

	private int arrayCount;

	private List<ReferenceType> throws_;

	private BlockStmt body;

    private boolean isDefault = false;

    public MethodDeclaration() {
	}

	public MethodDeclaration(final int modifiers, final Type type, final String name) {
		setModifiers(modifiers);
		setType(type);
		setName(name);
	}

	public MethodDeclaration(final int modifiers, final Type type, final String name, final List<Parameter> parameters) {
		setModifiers(modifiers);
		setType(type);
		setName(name);
		setParameters(parameters);
	}

	public MethodDeclaration(final int modifiers, final List<AnnotationExpr> annotations,
			final List<TypeParameter> typeParameters, final Type type, final String name,
			final List<Parameter> parameters, final int arrayCount, final List<ReferenceType> throws_, final BlockStmt body) {
		super(annotations);
		setModifiers(modifiers);
		setTypeParameters(typeParameters);
		setType(type);
		setName(name);
		setParameters(parameters);
		setArrayCount(arrayCount);
		setThrows(throws_);
		setBody(body);
	}

	public MethodDeclaration(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final int modifiers, final List<AnnotationExpr> annotations,
			final List<TypeParameter> typeParameters, final Type type, final String name,
			final List<Parameter> parameters, final int arrayCount, final List<ReferenceType> throws_, final BlockStmt body) {
		super(beginLine, beginColumn, endLine, endColumn, annotations);
		setModifiers(modifiers);
		setTypeParameters(typeParameters);
		setType(type);
		setName(name);
		setParameters(parameters);
		setArrayCount(arrayCount);
		setThrows(throws_);
		setBody(body);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public int getArrayCount() {
		return arrayCount;
	}

	public BlockStmt getBody() {
		return body;
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
		return name.getName();
	}

    public NameExpr getNameExpr() {
        return name;
    }

	public List<Parameter> getParameters() {
        parameters = ensureNotNull(parameters);
        return parameters;
	}

	public List<ReferenceType> getThrows() {
        throws_ = ensureNotNull(throws_);
        return throws_;
	}

	@Override
	public Type getType() {
		return type;
	}

	public List<TypeParameter> getTypeParameters() {
        typeParameters = ensureNotNull(typeParameters);
        return typeParameters;
	}

	public void setArrayCount(final int arrayCount) {
		this.arrayCount = arrayCount;
	}

	public void setBody(final BlockStmt body) {
		this.body = body;
		setAsParentNodeOf(this.body);
	}

	public void setModifiers(final int modifiers) {
		this.modifiers = modifiers;
	}

	public void setName(final String name) {
		this.name = new NameExpr(name);
	}

    public void setNameExpr(final NameExpr name) {
        this.name = name;
    }

    public void setParameters(final List<Parameter> parameters) {
		this.parameters = parameters;
		setAsParentNodeOf(this.parameters);
	}

	public void setThrows(final List<ReferenceType> throws_) {
		this.throws_ = throws_;
		setAsParentNodeOf(this.throws_);
	}

	@Override
	public void setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
	}

	public void setTypeParameters(final List<TypeParameter> typeParameters) {
		this.typeParameters = typeParameters;
		setAsParentNodeOf(typeParameters);
	}


    public boolean isDefault() {
        return isDefault;
    }

    public void setDefault(boolean isDefault) {
        this.isDefault = isDefault;
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
     * @return method declaration as String
     */
    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows, boolean includingParameterName) {
        StringBuffer sb = new StringBuffer();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = ModifierSet.getAccessSpecifier(getModifiers());
            sb.append(accessSpecifier.getCodeRepresenation());
            sb.append(accessSpecifier == AccessSpecifier.DEFAULT ? "" : " ");
            if (ModifierSet.isStatic(getModifiers())){
                sb.append("static ");
            }
            if (ModifierSet.isAbstract(getModifiers())){
                sb.append("abstract ");
            }
            if (ModifierSet.isFinal(getModifiers())){
                sb.append("final ");
            }
            if (ModifierSet.isNative(getModifiers())){
                sb.append("native ");
            }
            if (ModifierSet.isSynchronized(getModifiers())){
                sb.append("synchronized ");
            }
        }
        // TODO verify it does not print comments connected to the type
        sb.append(getType().toStringWithoutComments());
        sb.append(" ");
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
    public void setJavaDoc(JavadocComment javadocComment) {
        this.javadocComment = javadocComment;
    }

    @Override
    public JavadocComment getJavaDoc() {
        return javadocComment;
    }

    private JavadocComment javadocComment;
}
