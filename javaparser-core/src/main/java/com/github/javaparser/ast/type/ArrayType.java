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

package com.github.javaparser.ast.type;

import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Didier Villevalois
 */
public final class ArrayType extends ReferenceType {

    private Type componentType;

    public ArrayType() {
    }

    public ArrayType(Type componentType) {
        setComponentType(componentType);
    }

    public ArrayType(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
                     Type componentType) {
        super(beginLine, beginColumn, endLine, endColumn);
        setComponentType(componentType);
    }

    public ArrayType(int beginLine, int beginColumn, int endLine, int endColumn,
                     Type componentType, List<AnnotationExpr> annotations) {
        super(beginLine, beginColumn, endLine, endColumn, annotations);
        setComponentType(componentType);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Type getComponentType() {
        return componentType;
    }

    public void setComponentType(final Type componentType) {
        this.componentType = componentType;
        setAsParentNodeOf(this.componentType);
    }
}
