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
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class BlockStmt extends Statement implements NodeWithStatements<BlockStmt> {

    private NodeList<Statement> stmts;

    public BlockStmt() {
        this(Range.UNKNOWN, new NodeList<>());
    }

    public BlockStmt(final NodeList<Statement> stmts) {
        this(Range.UNKNOWN, stmts);

    }

    public BlockStmt(final Range range, final NodeList<Statement> stmts) {
        super(range);
        setStmts(stmts);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public NodeList<Statement> getStmts() {
        return stmts;
    }

    @Override
    public BlockStmt setStmts(final NodeList<Statement> stmts) {
        notifyPropertyChange("stmts", this.stmts, stmts);
        this.stmts = assertNotNull(stmts);
        setAsParentNodeOf(this.stmts);
        return this;
    }



}
