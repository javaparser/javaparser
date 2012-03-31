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
package japa.parser.ast.expr;

import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class UnaryExpr extends Expression {

	public static enum Operator {
		positive, // +
		negative, // -
		preIncrement, // ++
		preDecrement, // --
		not, // !
		inverse, // ~
		posIncrement, // ++
		posDecrement, // --
	}

	private Expression expr;

	private Operator op;

	public UnaryExpr() {
	}

	public UnaryExpr(final Expression expr, final Operator op) {
		setExpr(expr);
		setOperator(op);
	}

	public UnaryExpr(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final Expression expr, final Operator op) {
		super(beginLine, beginColumn, endLine, endColumn);
		setExpr(expr);
		setOperator(op);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Expression getExpr() {
		return expr;
	}

	public Operator getOperator() {
		return op;
	}

	public void setExpr(final Expression expr) {
		this.expr = expr;
		setAsParentNodeOf(this.expr);
	}

	public void setOperator(final Operator op) {
		this.op = op;
	}
}
