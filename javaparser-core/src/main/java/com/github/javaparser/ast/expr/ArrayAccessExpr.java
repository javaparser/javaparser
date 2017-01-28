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
 * Array brackets [] being used to get a value from an array.
 * In <br/><code>getNames()[15*15]</code> the name expression is getNames() and the index expression is 15*15.
 *
 * @author Julio Vilmar Gesser
 */
public final class ArrayAccessExpr extends Expression {

    private Expression name;

    private Expression index;

    public ArrayAccessExpr() {
        this(null, new NameExpr(), new IntegerLiteralExpr());
    }

    @AllFieldsConstructor
    public ArrayAccessExpr(Expression name, Expression index) {
        this(null, name, index);
    }

    public ArrayAccessExpr(Range range, Expression name, Expression index) {
        super(range);
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

    public ArrayAccessExpr setIndex(Expression index) {
        notifyPropertyChange(ObservableProperty.INDEX, this.index, index);
        this.index = assertNotNull(index);
        setAsParentNodeOf(this.index);
        return this;
    }

    public ArrayAccessExpr setName(Expression name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }
}
