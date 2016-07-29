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
 
package com.github.javaparser.ast.expr;

import static com.github.javaparser.Position.pos;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class Expression extends Node {

	public Expression() {
	}

	/**
	 * @deprecated prefer using Range objects.
	 */
	@Deprecated
	public Expression(final int beginLine, final int beginColumn, final int endLine, final int endColumn) {
		this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)));
	}
	
	public Expression(Range range) {
		super(range);
	}

}
