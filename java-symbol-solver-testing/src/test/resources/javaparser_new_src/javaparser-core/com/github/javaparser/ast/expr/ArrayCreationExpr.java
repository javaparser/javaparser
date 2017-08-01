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
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class ArrayCreationExpr extends Expression implements NodeWithType<ArrayCreationExpr> {

    private List<ArrayCreationLevel> levels;

    private Type type;

    private ArrayInitializerExpr initializer;

    public ArrayCreationExpr() {
    }

    public ArrayCreationExpr(Type type, List<ArrayCreationLevel> levels, ArrayInitializerExpr initializer) {
        setLevels(levels);
        setType(type);
        setInitializer(initializer);
    }

    public ArrayCreationExpr(Range range, Type type, List<ArrayCreationLevel> levels, ArrayInitializerExpr initializer) {
        super(range);
        setLevels(levels);
        setType(type);
        setInitializer(initializer);
    }

    public ArrayCreationExpr(Type type) {
        setType(type);
        setInitializer(null);
    }

    public ArrayCreationExpr(Range range, Type type) {
        super(range);
        setType(type);
        setInitializer(null);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public ArrayInitializerExpr getInitializer() {
        return initializer;
    }

    @Override
    public Type getType() {
        return type;
    }

    public ArrayCreationExpr setInitializer(ArrayInitializerExpr initializer) {
        this.initializer = initializer;
		setAsParentNodeOf(this.initializer);
        return this;
    }

    @Override
    public ArrayCreationExpr setType(Type type) {
        this.type = type;
		setAsParentNodeOf(this.type);
        return this;
    }

    public List<ArrayCreationLevel> getLevels() {
        levels = ensureNotNull(levels);
        return levels;
    }

    public ArrayCreationExpr setLevels(List<ArrayCreationLevel> levels) {
        this.levels = levels;
        setAsParentNodeOf(levels);
        return this;
    }
}
