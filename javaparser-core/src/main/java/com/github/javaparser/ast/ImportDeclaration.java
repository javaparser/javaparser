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
package com.github.javaparser.ast;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * An import declaration.
 * <br/><code>import com.github.javaparser.JavaParser;</code>
 * <br/><code>import com.github.javaparser.*;</code>
 * <br/><code>import com.github.javaparser.JavaParser.*; </code>
 * <br/><code>import static com.github.javaparser.JavaParser.*;</code> 
 * <br/><code>import static com.github.javaparser.JavaParser.parse;</code> 
 * 
 * <p>The name does not include the asterisk or the static keyword.</p>
 * @author Julio Vilmar Gesser
 */
public final class ImportDeclaration extends Node implements NodeWithName<ImportDeclaration> {

    private Name name;

    private boolean isStatic;

    private boolean isAsterisk;

    private ImportDeclaration() {
        this(null, new Name(), false, false);
    }

    @AllFieldsConstructor
    public ImportDeclaration(Name name, boolean isStatic, boolean isAsterisk) {
        this(null, name, isStatic, isAsterisk);
    }

    public ImportDeclaration(Range range, Name name, boolean isStatic, boolean isAsterisk) {
        super(range);
        setAsterisk(isAsterisk);
        setName(name);
        setStatic(isStatic);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    /**
     * Retrieves the name of the import (.* is not included.)
     */
    public Name getName() {
        return name;
    }

    /**
     * Return if the import ends with "*".
     */
    public boolean isAsterisk() {
        return isAsterisk;
    }

    public boolean isStatic() {
        return isStatic;
    }

    public ImportDeclaration setAsterisk(boolean asterisk) {
        notifyPropertyChange(ObservableProperty.IS_ASTERISK, this.isAsterisk, isAsterisk);
        this.isAsterisk = asterisk;
        return this;
    }

    public ImportDeclaration setName(Name name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = name;
        setAsParentNodeOf(this.name);
        return this;
    }

    public ImportDeclaration setStatic(boolean isStatic) {
        notifyPropertyChange(ObservableProperty.IS_STATIC, this.isStatic, isStatic);
        this.isStatic = isStatic;
        return this;
    }
}

