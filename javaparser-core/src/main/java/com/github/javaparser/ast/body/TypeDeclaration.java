/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class TypeDeclaration extends BodyDeclaration {

	private NameExpr name;

	private int modifiers;

	private List<BodyDeclaration> members;

	public TypeDeclaration() {
	}

	public TypeDeclaration(int modifiers, String name) {
		setName(name);
		setModifiers(modifiers);
	}

	public TypeDeclaration(List<AnnotationExpr> annotations,
			int modifiers, String name,
			List<BodyDeclaration> members) {
		super(annotations);
		setName(name);
		setModifiers(modifiers);
		setMembers(members);
	}

	public TypeDeclaration(Lexeme first, Lexeme last, List<AnnotationExpr> annotations,
			int modifiers, String name,
			List<BodyDeclaration> members) {
		super(first, last, annotations);
		setName(name);
		setModifiers(modifiers);
		setMembers(members);
	}

	public final List<BodyDeclaration> getMembers() {
		return members;
	}

	/**
	 * Return the modifiers of this type declaration.
	 * 
	 * @see ModifierSet
	 * @return modifiers
	 */
	public final int getModifiers() {
		return modifiers;
	}

	public final String getName() {
		return name.getName();
	}

	public void setMembers(List<BodyDeclaration> members) {
		this.members = members;
		setAsParentNodeOf(this.members);
	}

	public final void setModifiers(int modifiers) {
		this.modifiers = modifiers;
	}

	public final void setName(String name) {
		this.name = new NameExpr(name);
	}

    public final void setNameExpr(NameExpr nameExpr) {
      this.name = nameExpr;
    }

    public final NameExpr getNameExpr() {
      return name;
    }
}
