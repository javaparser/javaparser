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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithElementType;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Pair;

import java.util.Optional;

import static com.github.javaparser.ast.type.ArrayType.wrapInArrayTypes;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarator extends Node implements
        NodeWithType<VariableDeclarator, Type<?>> {

    private VariableDeclaratorId id;

    private Expression init;

    public VariableDeclarator() {
        this(Range.UNKNOWN, new VariableDeclaratorId(), null);
    }

    public VariableDeclarator(VariableDeclaratorId id) {
        this(Range.UNKNOWN, id, null);
    }

    public VariableDeclarator(String variableName) {
        this(Range.UNKNOWN, new VariableDeclaratorId(variableName), null);
    }

    /**
     * Defines the declaration of a variable.
     *
     * @param id The identifier for this variable. IE. The variables name.
     * @param init What this variable should be initialized to. An {@link com.github.javaparser.ast.expr.AssignExpr} is
     * unnecessary as the <code>=</code> operator is already added.
     */
    public VariableDeclarator(VariableDeclaratorId id, Expression init) {
        this(Range.UNKNOWN, id, init);
    }

    public VariableDeclarator(String variableName, Expression init) {
        this(Range.UNKNOWN, new VariableDeclaratorId(variableName), init);
    }

    public VariableDeclarator(Range range, VariableDeclaratorId id, Expression init) {
        super(range);
        setId(id);
        setInit(init);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public VariableDeclaratorId getId() {
        return id;
    }

    public Optional<Expression> getInit() {
        return Optional.ofNullable(init);
    }

    public VariableDeclarator setId(VariableDeclaratorId id) {
        notifyPropertyChange(ObservableProperty.ID, this.id, id);
        this.id = assertNotNull(id);
        setAsParentNodeOf(this.id);
        return this;
    }

    /**
     * Sets the init expression
     *
     * @param init the init expression, can be null
     * @return this, the VariableDeclarator
     */
    public VariableDeclarator setInit(Expression init) {
        notifyPropertyChange(ObservableProperty.INIT, this.init, init);
        this.init = init;
        setAsParentNodeOf(this.init);
        return this;
    }

    /**
     * Will create a {@link NameExpr} with the init param
     *
     * @param init the init expression, can be null
     * @return this, the VariableDeclarator
     */
    public VariableDeclarator setInit(String init) {
        NameExpr newInit = new NameExpr(assertNotNull(init));
        notifyPropertyChange(ObservableProperty.INIT, this.init, newInit);
        this.init = newInit;
        setAsParentNodeOf(this.init);
        return this;
    }


    @Override
    public Type getType() {
        NodeWithElementType<?> elementType = getAncestorOfType(NodeWithElementType.class);

        return wrapInArrayTypes((Type<?>) elementType.getElementType().clone(),
                elementType.getArrayBracketPairsAfterElementType(),
                getId().getArrayBracketPairsAfterId());
    }

    @Override
    public VariableDeclarator setType(Type<?> type) {
        Pair<Type<?>, NodeList<ArrayBracketPair>> unwrapped = ArrayType.unwrapArrayTypes(type);
        NodeWithElementType<?> nodeWithElementType = getAncestorOfType(NodeWithElementType.class);
        if (nodeWithElementType == null) {
            throw new IllegalStateException("Cannot set type without a parent");
        }
        nodeWithElementType.setElementType(unwrapped.a);
        nodeWithElementType.setArrayBracketPairsAfterElementType(new NodeList<>());
        getId().setArrayBracketPairsAfterId(unwrapped.b);
        return this;
    }
}
