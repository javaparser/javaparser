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
package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;

/**
 * An expression with an expression on the left, an expression on the right, and an operator in the middle.
 * It supports the operators that are found the the BinaryExpr.Operator enum.
 * <br/><code>a && b</code>
 * <br/><code>155 * 33</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class BinaryExpr extends Expression {

    public enum Operator {

        OR("||"), AND("&&"), BINARY_OR("|"), BINARY_AND("&"), XOR("^"), EQUALS("=="), NOT_EQUALS("!="), LESS("<"), GREATER(">"), LESS_EQUALS("<="), GREATER_EQUALS(">="), LEFT_SHIFT("<<"), SIGNED_RIGHT_SHIFT(">>"), UNSIGNED_RIGHT_SHIFT(">>>"), PLUS("+"), MINUS("-"), MULTIPLY("*"), DIVIDE("/"), REMAINDER("%");

        private final String codeRepresentation;

        Operator(String codeRepresentation) {
            this.codeRepresentation = codeRepresentation;
        }

        public String asString() {
            return codeRepresentation;
        }
    }

    private Expression left;

    private Expression right;

    private Operator operator;

    public BinaryExpr() {
        this(null, new BooleanLiteralExpr(), new BooleanLiteralExpr(), Operator.EQUALS);
    }

    @AllFieldsConstructor
    public BinaryExpr(Expression left, Expression right, Operator operator) {
        this(null, left, right, operator);
    }

    public BinaryExpr(Range range, Expression left, Expression right, Operator operator) {
        super(range);
        setLeft(left);
        setRight(right);
        setOperator(operator);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Expression getLeft() {
        return left;
    }

    public Operator getOperator() {
        return operator;
    }

    public Expression getRight() {
        return right;
    }

    public BinaryExpr setLeft(final Expression left) {
        assertNotNull(left);
        notifyPropertyChange(ObservableProperty.LEFT, this.left, left);
        if (this.left != null)
            this.left.setParentNode(null);
        this.left = left;
        setAsParentNodeOf(left);
        return this;
    }

    public BinaryExpr setOperator(final Operator operator) {
        assertNotNull(operator);
        notifyPropertyChange(ObservableProperty.OPERATOR, this.operator, operator);
        this.operator = operator;
        return this;
    }

    public BinaryExpr setRight(final Expression right) {
        assertNotNull(right);
        notifyPropertyChange(ObservableProperty.RIGHT, this.right, right);
        if (this.right != null)
            this.right.setParentNode(null);
        this.right = right;
        setAsParentNodeOf(right);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }
}

