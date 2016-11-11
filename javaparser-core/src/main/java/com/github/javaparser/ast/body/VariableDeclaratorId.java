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
 
package com.github.javaparser.ast.body;

import com.github.javaparser.Range;
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Arrays;
import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclaratorId extends Node implements NodeWithSimpleName<VariableDeclaratorId> {

    private SimpleName name;

    private NodeList<ArrayBracketPair> arrayBracketPairsAfterId;

    public VariableDeclaratorId() {
        this(Range.UNKNOWN,
                new SimpleName(),
                new NodeList<>());
    }

    public VariableDeclaratorId(String name) {
        this(Range.UNKNOWN,
                new SimpleName(name),
                new NodeList<>());
    }

    public VariableDeclaratorId(SimpleName name) {
        this(Range.UNKNOWN,
                name,
                new NodeList<>());
    }

    public VariableDeclaratorId(Range range, SimpleName name, NodeList<ArrayBracketPair> arrayBracketPairsAfterId) {
        super(range);
        setName(name);
        setArrayBracketPairsAfterId(assertNotNull(arrayBracketPairsAfterId));
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    @Override
    public VariableDeclaratorId setName(SimpleName name) {
        notifyPropertyChange("name", this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
        return this;
    }

    public NodeList<ArrayBracketPair> getArrayBracketPairsAfterId() {
        return arrayBracketPairsAfterId;
    }

    public VariableDeclaratorId setArrayBracketPairsAfterId(NodeList<ArrayBracketPair> arrayBracketPairsAfterId) {
        notifyPropertyChange("arrayBracketPairsAfterId", this.arrayBracketPairsAfterId, arrayBracketPairsAfterId);
        this.arrayBracketPairsAfterId = assertNotNull(arrayBracketPairsAfterId);
        setAsParentNodeOf(arrayBracketPairsAfterId);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(arrayBracketPairsAfterId);
    }
}
