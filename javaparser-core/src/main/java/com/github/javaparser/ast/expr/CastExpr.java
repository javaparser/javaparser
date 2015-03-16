/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class CastExpr extends Expression {

    private Type type;

    private Expression expr;

    public CastExpr() {
    }

    public CastExpr(Type type, Expression expr) {
    	setType(type);
    	setExpr(expr);
    }

    public CastExpr(Lexeme first, Lexeme last, Type type, Expression expr) {
        super(first, last);
        setType(type);
    	setExpr(expr);
    }

	@Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Expression getExpr() {
        return expr;
    }

    public Type getType() {
        return type;
    }

    public void setExpr(Expression expr) {
        this.expr = expr;
		setAsParentNodeOf(this.expr);
    }

    public void setType(Type type) {
        this.type = type;
		setAsParentNodeOf(this.type);
    }
}
