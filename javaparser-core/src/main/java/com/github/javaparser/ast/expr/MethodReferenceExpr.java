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
 
package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.ast.internal.Utils.*;

/**
 * Method reference expressions introduced in Java 8 specifically designed to simplify lambda Expressions.
 * These are some examples:
 *
 * System.out::println; 
 *
 * (test ? stream.map(String::trim) : stream)::toArray; 
 * @author Raquel Pau
 *
 */
public class MethodReferenceExpr extends Expression {

    private Expression scope;

    private List<TypeParameter> typeParameters;

    private String identifier;

    public MethodReferenceExpr() {
    }

    public MethodReferenceExpr(int beginLine, int beginColumn, int endLine,
                               int endColumn, Expression scope,
                               List<TypeParameter> typeParameters, String identifier) {

        super(beginLine, beginColumn, endLine, endColumn);
        setIdentifier(identifier);
        setScope(scope);
        setTypeParameters(typeParameters);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {

        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Expression getScope() {
        return scope;
    }

    public void setScope(Expression scope) {
        this.scope = scope;
        setAsParentNodeOf(this.scope);
    }

    public List<TypeParameter> getTypeParameters() {
        typeParameters = ensureNotNull(typeParameters);
        return typeParameters;
    }

    public void setTypeParameters(List<TypeParameter> typeParameters) {
        this.typeParameters = typeParameters;
        setAsParentNodeOf(this.typeParameters);
    }

    public String getIdentifier() {
        return identifier;
    }

    public void setIdentifier(String identifier) {
        this.identifier = identifier;
    }

}
