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
 
package com.github.javaparser.ast.stmt;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;

import static com.github.javaparser.utils.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class TryStmt extends Statement {
	
	private NodeList<VariableDeclarationExpr> resources;

    // TODO can be null
	private BlockStmt tryBlock;

	private NodeList<CatchClause> catchs;

    // TODO can be null
	private BlockStmt finallyBlock;

	public TryStmt() {
		this(Range.UNKNOWN,
				new NodeList<>(),
				new BlockStmt(),
				new NodeList<>(),
				new BlockStmt());
	}

	public TryStmt(final BlockStmt tryBlock, final NodeList<CatchClause> catchs,
			final BlockStmt finallyBlock) {
		this(Range.UNKNOWN,
				new NodeList<>(),
				tryBlock,
				catchs,
				finallyBlock);
	}

	public TryStmt(Range range, NodeList<VariableDeclarationExpr> resources,
	               final BlockStmt tryBlock, final NodeList<CatchClause> catchs, final BlockStmt finallyBlock) {
		super(range);
		setResources(resources);
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

	public NodeList<CatchClause> getCatchs() {
        return catchs;
	}

	public BlockStmt getFinallyBlock() {
		return finallyBlock;
	}

	public BlockStmt getTryBlock() {
		return tryBlock;
	}
	
	public NodeList<VariableDeclarationExpr> getResources() {
        return resources;
	}

	public TryStmt setCatchs(final NodeList<CatchClause> catchs) {
		this.catchs = assertNotNull(catchs);
		setAsParentNodeOf(this.catchs);
		return this;
	}

	public TryStmt setFinallyBlock(final BlockStmt finallyBlock) {
		this.finallyBlock = finallyBlock;
		setAsParentNodeOf(this.finallyBlock);
		return this;
	}

	public TryStmt setTryBlock(final BlockStmt tryBlock) {
		this.tryBlock = tryBlock;
		setAsParentNodeOf(this.tryBlock);
		return this;
	}
	
	public TryStmt setResources(NodeList<VariableDeclarationExpr> resources) {
		this.resources = assertNotNull(resources);
		setAsParentNodeOf(this.resources);
		return this;
	}
}
