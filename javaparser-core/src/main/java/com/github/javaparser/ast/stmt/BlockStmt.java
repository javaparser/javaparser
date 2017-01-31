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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Statements in between { and }.
 *
 * @author Julio Vilmar Gesser
 */
public final class BlockStmt extends Statement implements NodeWithStatements<BlockStmt> {

    private NodeList<Statement> statements;

    public BlockStmt() {
        this(null, new NodeList<>());
    }

    @AllFieldsConstructor
    public BlockStmt(final NodeList<Statement> statements) {
        this(null, statements);
    }

    public BlockStmt(final Range range, final NodeList<Statement> statements) {
        super(range);
        setStatements(statements);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public NodeList<Statement> getStatements() {
        return statements;
    }

    public BlockStmt setStatements(final NodeList<Statement> statements) {
        assertNotNull(statements);
        notifyPropertyChange(ObservableProperty.STATEMENTS, this.statements, statements);
        this.statements = statements;
        setAsParentNodeOf(statements);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getStatements());
    }
}

