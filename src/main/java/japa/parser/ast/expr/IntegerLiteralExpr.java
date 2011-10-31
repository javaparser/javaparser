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
 * Created on 02/03/2007
 */
package japa.parser.ast.expr;

import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public class IntegerLiteralExpr extends StringLiteralExpr {

	private static final String UNSIGNED_MIN_VALUE = "2147483648";

	protected static final String MIN_VALUE = "-" + UNSIGNED_MIN_VALUE;

	public IntegerLiteralExpr() {
	}

	public IntegerLiteralExpr(final String value) {
		super(value);
	}

	public IntegerLiteralExpr(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final String value) {
		super(beginLine, beginColumn, endLine, endColumn, value);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public final boolean isMinValue() {
		return value != null && //
				value.length() == 10 && //
				value.equals(UNSIGNED_MIN_VALUE);
	}
}
