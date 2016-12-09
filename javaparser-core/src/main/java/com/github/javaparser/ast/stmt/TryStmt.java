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
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class TryStmt extends Statement {

    private NodeList<VariableDeclarationExpr> resources;

    private BlockStmt tryBlock;

    private NodeList<CatchClause> catchClauses;

    private BlockStmt finallyBlock;

    public TryStmt() {
        this(null,
                new NodeList<>(),
                new BlockStmt(),
                new NodeList<>(),
                null);
    }

    public TryStmt(final BlockStmt tryBlock, final NodeList<CatchClause> catchClauses,
                   final BlockStmt finallyBlock) {
        this(null,
                new NodeList<>(),
                tryBlock,
                catchClauses,
                finallyBlock);
    }

    public TryStmt(Range range, NodeList<VariableDeclarationExpr> resources,
                   final BlockStmt tryBlock, final NodeList<CatchClause> catchClauses, final BlockStmt finallyBlock) {
        super(range);
        setResources(resources);
        setTryBlock(tryBlock);
        setCatchClauses(catchClauses);
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

    public NodeList<CatchClause> getCatchClauses() {
        return catchClauses;
    }

    public Optional<BlockStmt> getFinallyBlock() {
        return Optional.ofNullable(finallyBlock);
    }

    public Optional<BlockStmt> getTryBlock() {
        return Optional.ofNullable(tryBlock);
    }

    public NodeList<VariableDeclarationExpr> getResources() {
        return resources;
    }

    public TryStmt setCatchClauses(final NodeList<CatchClause> catchClauses) {
        notifyPropertyChange(ObservableProperty.CATCH_CLAUSES, this.catchClauses, catchClauses);
        this.catchClauses = assertNotNull(catchClauses);
        setAsParentNodeOf(this.catchClauses);
        return this;
    }

    public TryStmt setFinallyBlock(final BlockStmt finallyBlock) {
        notifyPropertyChange(ObservableProperty.FINALLY_BLOCK, this.finallyBlock, finallyBlock);
        this.finallyBlock = finallyBlock;
        setAsParentNodeOf(this.finallyBlock);
        return this;
    }

    public TryStmt setTryBlock(final BlockStmt tryBlock) {
        notifyPropertyChange(ObservableProperty.TRY_BLOCK, this.tryBlock, tryBlock);
        this.tryBlock = tryBlock;
        setAsParentNodeOf(this.tryBlock);
        return this;
    }

    public TryStmt setResources(NodeList<VariableDeclarationExpr> resources) {
        notifyPropertyChange(ObservableProperty.RESOURCES, this.resources, resources);
        this.resources = assertNotNull(resources);
        setAsParentNodeOf(this.resources);
        return this;
    }
}
