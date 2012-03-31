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
 * Created on 18/11/2006
 */
package japa.parser.ast.stmt;

import japa.parser.ast.Node;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class CatchClause extends Node {

	private Parameter except;

	private BlockStmt catchBlock;

	public CatchClause() {
	}

	public CatchClause(final Parameter except, final BlockStmt catchBlock) {
		setExcept(except);
		setCatchBlock(catchBlock);
	}

	public CatchClause(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
			final Parameter except, final BlockStmt catchBlock) {
		super(beginLine, beginColumn, endLine, endColumn);
		setExcept(except);
		setCatchBlock(catchBlock);
	}

	@Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public BlockStmt getCatchBlock() {
		return catchBlock;
	}

	public Parameter getExcept() {
		return except;
	}

	public void setCatchBlock(final BlockStmt catchBlock) {
		this.catchBlock = catchBlock;
		setAsParentNodeOf(this.catchBlock);
	}

	public void setExcept(final Parameter except) {
		this.except = except;
		setAsParentNodeOf(this.except);
	}
}
