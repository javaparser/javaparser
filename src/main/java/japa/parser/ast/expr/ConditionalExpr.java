/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 05/10/2006
 */
package japa.parser.ast.expr;

import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class ConditionalExpr extends Expression {

    private Expression condition;

    private Expression thenExpr;

    private Expression elseExpr;

    public ConditionalExpr() {
    }

    public ConditionalExpr(Expression condition, Expression thenExpr, Expression elseExpr) {
        setCondition(condition);
        setThenExpr(thenExpr);
        setElseExpr(elseExpr);
    }

    public ConditionalExpr(int beginLine, int beginColumn, int endLine, int endColumn, Expression condition, Expression thenExpr, Expression elseExpr) {
        super(beginLine, beginColumn, endLine, endColumn);
        setCondition(condition);
        setThenExpr(thenExpr);
        setElseExpr(elseExpr);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Expression getCondition() {
        return condition;
    }

    public Expression getElseExpr() {
        return elseExpr;
    }

    public Expression getThenExpr() {
        return thenExpr;
    }

    public void setCondition(Expression condition) {
        this.condition = condition;
		setAsParentNodeOf(this.condition);
    }

    public void setElseExpr(Expression elseExpr) {
        this.elseExpr = elseExpr;
		setAsParentNodeOf(this.elseExpr);
    }

    public void setThenExpr(Expression thenExpr) {
        this.thenExpr = thenExpr;
		setAsParentNodeOf(this.thenExpr);
    }
}
