/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 05/10/2006
 */
package japa.parser.ast.body;

import japa.parser.ast.TypeParameter;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.expr.NameExpr;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.type.Type;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends BodyDeclaration {

	private int modifiers;

	private List<TypeParameter> typeParameters;

	private Type type;

	private NameExpr name;

	private List<Parameter> parameters;

	private int arrayCount;

	private List<NameExpr> throws_;

	private BlockStmt body;

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

	public MethodDeclaration(final JavadocComment javaDoc, final int modifiers, final List<AnnotationExpr> annotations,
			final List<TypeParameter> typeParameters, final Type type, final String name,
			final List<Parameter> parameters, final int arrayCount, final List<NameExpr> throws_, final BlockStmt block) {
		super(annotations, javaDoc);
		setModifiers(modifiers);
		setTypeParameters(typeParameters);
		setType(type);
		setName(name);
		setParameters(parameters);
		setArrayCount(arrayCount);
		setThrows(throws_);
		setBody(block);
	}

	public MethodDeclaration(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final JavadocComment javaDoc, final int modifiers, final List<AnnotationExpr> annotations,
			final List<TypeParameter> typeParameters, final Type type, final String name,
			final List<Parameter> parameters, final int arrayCount, final List<NameExpr> throws_, final BlockStmt block) {
		super(beginLine, beginColumn, endLine, endColumn, annotations, javaDoc);
		setModifiers(modifiers);
		setTypeParameters(typeParameters);
		setType(type);
		setName(name);
		setParameters(parameters);
		setArrayCount(arrayCount);
		setThrows(throws_);
		setBody(block);
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

	// FIXME this is called "Block" in the constructor. Pick one.
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

	public String getName() {
		return name.getName();
	}

    public NameExpr getNameExpr() {
        return name;
    }

	public List<Parameter> getParameters() {
		return parameters;
	}

	public List<NameExpr> getThrows() {
		return throws_;
	}

	public Type getType() {
		return type;
	}

	public List<TypeParameter> getTypeParameters() {
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

	public void setThrows(final List<NameExpr> throws_) {
		this.throws_ = throws_;
		setAsParentNodeOf(this.throws_);
	}

	public void setType(final Type type) {
		this.type = type;
		setAsParentNodeOf(this.type);
	}

	public void setTypeParameters(final List<TypeParameter> typeParameters) {
		this.typeParameters = typeParameters;
		setAsParentNodeOf(typeParameters);
	}
}
