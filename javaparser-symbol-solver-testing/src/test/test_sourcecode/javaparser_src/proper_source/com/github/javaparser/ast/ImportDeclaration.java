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
 
package com.github.javaparser.ast;

import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * <p>
 * This class represents a import declaration. Imports are optional for the
 * {@link CompilationUnit}.
 * </p>
 * The ImportDeclaration is constructed following the syntax:<br>
 * <pre>
 * {@code
 * ImportDeclaration ::= "import" ( "static" )? }{@link NameExpr}{@code ( "." "*" )? ";"
 * }
 * </pre>
 * @author Julio Vilmar Gesser
 */
public final class ImportDeclaration extends Node {

    private NameExpr name;

    private boolean static_;

    private boolean asterisk;

    public ImportDeclaration() {
    }

    public ImportDeclaration(NameExpr name, boolean isStatic, boolean isAsterisk) {
        setAsterisk(isAsterisk);
        setName(name);
        setStatic(isStatic);
    }

    public ImportDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, NameExpr name, boolean isStatic, boolean isAsterisk) {
        super(beginLine, beginColumn, endLine, endColumn);
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
     * Retrieves the name of the import.
     * 
     * @return the name of the import
     */
    public NameExpr getName() {
        return name;
    }

    /**
     * Return if the import ends with "*".
     * 
     * @return <code>true</code> if the import ends with "*", <code>false</code>
     *         otherwise
     */
    public boolean isAsterisk() {
        return asterisk;
    }

    /**
     * Return if the import is static.
     * 
     * @return <code>true</code> if the import is static, <code>false</code>
     *         otherwise
     */
    public boolean isStatic() {
        return static_;
    }

    /**
     * Sets if this import is asterisk.
     * 
     * @param asterisk
     *            <code>true</code> if this import is asterisk
     */
    public void setAsterisk(boolean asterisk) {
        this.asterisk = asterisk;
    }

    /**
     * Sets the name this import.
     * 
     * @param name
     *            the name to set
     */
    public void setName(NameExpr name) {
        this.name = name;
        setAsParentNodeOf(this.name);
    }

    /**
     * Sets if this import is static.
     * 
     * @param static_
     *            <code>true</code> if this import is static
     */
    public void setStatic(boolean static_) {
        this.static_ = static_;
    }

}
