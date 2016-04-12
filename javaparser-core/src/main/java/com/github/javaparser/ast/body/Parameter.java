/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class Parameter extends BaseParameter implements TypedNode {
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

    public Parameter(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, Type type, boolean isVarArgs, VariableDeclaratorId id) {
        super(beginLine, beginColumn, endLine, endColumn, modifiers, annotations, id);
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

    @Override
    public Type getType() {
        return type;
    }

    public boolean isVarArgs() {
        return isVarArgs;
    }

    @Override
    public void setType(Type type) {
        this.type = type;
		setAsParentNodeOf(this.type);
    }

    public void setVarArgs(boolean isVarArgs) {
        this.isVarArgs = isVarArgs;
    }
}
