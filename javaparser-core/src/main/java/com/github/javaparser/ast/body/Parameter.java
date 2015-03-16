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

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class Parameter extends BaseParameter {
    private Type type;

    private boolean isVarArgs;

    public Parameter() {
    }

    public Parameter(Type type, VariableDeclaratorId id) {
    	super(id);
        setType(type);
    }

    public Parameter(int modifiers, Type type, VariableDeclaratorId id) {
    	super(modifiers, id);
        setType(type);
    }

	public Parameter(Lexeme first, Lexeme last, int modifiers, List<AnnotationExpr> annotations, Type type, boolean isVarArgs, VariableDeclaratorId id) {
		super(first, last, modifiers, annotations, id);
		setType(type);
		setVarArgs(isVarArgs);
	}

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Type getType() {
        return type;
    }

    public boolean isVarArgs() {
        return isVarArgs;
    }

    public void setType(Type type) {
        this.type = type;
		setAsParentNodeOf(this.type);
    }

    public void setVarArgs(boolean isVarArgs) {
        this.isVarArgs = isVarArgs;
    }
}
