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

/**
 * An assignment expression. It supports the operators that are found the the AssignExpr.Operator enum.
 * <br/><code>a=5</code>
 * <br/><code>time+=500</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class AssignExpr extends Expression {

    public enum Operator {

        ASSIGN("="), PLUS("+="), MINUS("-="), MULTIPLY("*="), DIVIDE("/="), AND("&="), OR("|="), XOR("^="), REMAINDER("%="), LEFT_SHIFT("<<="), SIGNED_RIGHT_SHIFT(">>="), UNSIGNED_RIGHT_SHIFT(">>>=");

        private final String codeRepresentation;

        Operator(String codeRepresentation) {
            this.codeRepresentation = codeRepresentation;
        }

        public String asString() {
            return codeRepresentation;
        }
    }

    private Expression target;

    private Expression value;

    private Operator operator;

    public AssignExpr() {
        this(null, new NameExpr(), new StringLiteralExpr(), Operator.ASSIGN);
    }

    @AllFieldsConstructor
    public AssignExpr(Expression target, Expression value, Operator operator) {
        this(null, target, value, operator);
    }

    public AssignExpr(Range range, Expression target, Expression value, Operator operator) {
        super(range);
        setTarget(target);
        setValue(value);
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

    public Operator getOperator() {
        return operator;
    }

    public Expression getTarget() {
        return target;
    }

    public Expression getValue() {
        return value;
    }

    public AssignExpr setOperator(final Operator operator) {
        assertNotNull(operator);
        notifyPropertyChange(ObservableProperty.OPERATOR, this.operator, operator);
        this.operator = operator;
        return this;
    }

    public AssignExpr setTarget(final Expression target) {
        assertNotNull(target);
        notifyPropertyChange(ObservableProperty.TARGET, this.target, target);
        this.target = target;
        setAsParentNodeOf(target);
        return this;
    }

    public AssignExpr setValue(final Expression value) {
        assertNotNull(value);
        notifyPropertyChange(ObservableProperty.VALUE, this.value, value);
        this.value = value;
        setAsParentNodeOf(value);
        return this;
    }
}

