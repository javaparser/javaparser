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
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class BinaryExpr extends Expression {

    public enum Operator {
        OR("||"),
        AND("&&"),
        BINARY_OR("|"),
        BINARY_AND("&"),
        XOR("^"),
        EQUALS("=="),
        NOT_EQUALS("!="),
        LESS("<"),
        GREATER(">"),
        LESS_EQUALS("<="),
        GREATER_EQUALS(">="),
        LEFT_SHIFT("<<"),
        SIGNED_RIGHT_SHIFT(">>"),
        UNSIGNED_RIGHT_SHIFT(">>>"),
        PLUS("+"),
        MINUS("-"),
        MULTIPLY("*"),
        DIVIDE("/"),
        MODULO("%");

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

    public BinaryExpr setLeft(Expression left) {
        notifyPropertyChange(ObservableProperty.LEFT, this.left, left);
        this.left = left;
		setAsParentNodeOf(this.left);
        return this;
    }

    public BinaryExpr setOperator(Operator op) {
        notifyPropertyChange(ObservableProperty.OPERATOR, this.operator, op);
        this.operator = op;
        return this;
    }

    public BinaryExpr setRight(Expression right) {
        notifyPropertyChange(ObservableProperty.RIGHT, this.right, right);
        this.right = right;
		setAsParentNodeOf(this.right);
        return this;
    }
}
