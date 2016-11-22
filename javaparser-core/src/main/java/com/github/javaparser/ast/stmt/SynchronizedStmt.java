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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class SynchronizedStmt extends Statement implements NodeWithBlockStmt<SynchronizedStmt> {

    private Expression expr;

    private BlockStmt block;

    public SynchronizedStmt() {
        this(null, new NameExpr(), new BlockStmt());
    }

    public SynchronizedStmt(final Expression expr, final BlockStmt block) {
        this(null, expr, block);
    }

    public SynchronizedStmt(Range range, final Expression expr, final BlockStmt block) {
        super(range);
        setExpr(expr);
        setBody(block);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * @deprecated use {@link #getBody()}
     */
    @Deprecated
    public BlockStmt getBlock() {
        return block;
    }

    public Expression getExpr() {
        return expr;
    }

    /**
     * @deprecated Use {@link #setBody(BlockStmt)} instead
     */
    @Deprecated
    public SynchronizedStmt setBlock(final BlockStmt block) {
        return setBody(block);
    }

    public SynchronizedStmt setExpr(final Expression expr) {
        notifyPropertyChange(ObservableProperty.EXPR, this.expr, expr);
        this.expr = assertNotNull(expr);
        setAsParentNodeOf(this.expr);
        return this;
    }

    @Override
    public BlockStmt getBody() {
        return block;
    }

    @Override
    public SynchronizedStmt setBody(BlockStmt block) {
        notifyPropertyChange(ObservableProperty.BLOCK, this.block, block);
        this.block = assertNotNull(block);
        setAsParentNodeOf(this.block);
        return this;
    }
}
