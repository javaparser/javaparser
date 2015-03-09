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

package com.github.javaparser.ast.expr;

import com.github.javaparser.Position;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class AnnotationExpr extends Expression {

	protected NameExpr name;

	public AnnotationExpr() {}

	public AnnotationExpr(int beginLine, int beginColumn, int endLine,
			int endColumn) {
		super(beginLine, beginColumn, endLine, endColumn);
	}

	public AnnotationExpr(Position begin, Position end) {
		super(begin, end);
	}

	public NameExpr getName() {
		return name;
	}

	public void setName(NameExpr name) {
		this.name = name;
		setAsParentNodeOf(name);
	}
}
