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
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class ArrayAccessExpr extends Expression {

    private Expression name;

    private Expression index;

    public ArrayAccessExpr() {
    }

    public ArrayAccessExpr(Expression name, Expression index) {
        setName(name);
        setIndex(index);
    }

    public ArrayAccessExpr(Lexeme first, Lexeme last, Expression name, Expression index) {
        super(first, last);
        setName(name);
        setIndex(index);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Expression getIndex() {
        return index;
    }

    public Expression getName() {
        return name;
    }

    public void setIndex(Expression index) {
        this.index = index;
		setAsParentNodeOf(this.index);
    }

    public void setName(Expression name) {
        this.name = name;
		setAsParentNodeOf(this.name);
    }
}
