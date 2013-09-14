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

import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;
import japa.parser.ast.expr.VariableDeclarationExpr;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class TryStmt extends Statement {
	
	private List<VariableDeclarationExpr> resources;

	private BlockStmt tryBlock;

	private List<CatchClause> catchs;

	private BlockStmt finallyBlock;

	public TryStmt() {
	}

	public TryStmt(final BlockStmt tryBlock, final List<CatchClause> catchs,
			final BlockStmt finallyBlock) {
		setTryBlock(tryBlock);
		setCatchs(catchs);
		setFinallyBlock(finallyBlock);
	}

	public TryStmt(final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, List<VariableDeclarationExpr> resources,
			final BlockStmt tryBlock, final List<CatchClause> catchs, final BlockStmt finallyBlock) {
		super(beginLine, beginColumn, endLine, endColumn);
		this.resources = resources;
		setTryBlock(tryBlock);
		setCatchs(catchs);
		setFinallyBlock(finallyBlock);
	}

	@Override
	public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public List<CatchClause> getCatchs() {
		return catchs;
	}

	public BlockStmt getFinallyBlock() {
		return finallyBlock;
	}

	public BlockStmt getTryBlock() {
		return tryBlock;
	}
	
	public List<VariableDeclarationExpr> getResources() {
		return resources;
	}

	public void setCatchs(final List<CatchClause> catchs) {
		this.catchs = catchs;
		setAsParentNodeOf(this.catchs);
	}

	public void setFinallyBlock(final BlockStmt finallyBlock) {
		this.finallyBlock = finallyBlock;
		setAsParentNodeOf(this.finallyBlock);
	}

	public void setTryBlock(final BlockStmt tryBlock) {
		this.tryBlock = tryBlock;
		setAsParentNodeOf(this.tryBlock);
	}
	
	public void setResources(List<VariableDeclarationExpr> resources) {
		this.resources = resources;
	}
}
