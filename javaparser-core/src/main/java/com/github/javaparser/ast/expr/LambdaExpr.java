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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Lambda expression.
 *
 * @author Raquel Pau
 */
public class LambdaExpr extends Expression implements
        NodeWithParameters<LambdaExpr> {

    private NodeList<Parameter> parameters;

    private boolean isEnclosingParameters;

    private Statement body;

    public LambdaExpr() {
        this(null,
                new NodeList<>(),
                new ReturnStmt(),
                false);
    }

    public LambdaExpr(Range range, NodeList<Parameter> parameters, Statement body,
                      boolean isEnclosingParameters) {

        super(range);
        setParameters(parameters);
        setBody(body);
        setEnclosingParameters(isEnclosingParameters);
    }

    @Override
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    @Override
    public LambdaExpr setParameters(NodeList<Parameter> parameters) {
        notifyPropertyChange(ObservableProperty.PARAMETERS, this.parameters, parameters);
        this.parameters = assertNotNull(parameters);
        setAsParentNodeOf(this.parameters);
        return this;
    }

    public Statement getBody() {
        return body;
    }

    public LambdaExpr setBody(Statement body) {
        this.body = body;
        setAsParentNodeOf(this.body);
        return this;
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public boolean isEnclosingParameters() {
        return isEnclosingParameters;
    }

    public LambdaExpr setEnclosingParameters(boolean enclosingParameters) {
        notifyPropertyChange(ObservableProperty.ENCLOSING_PARAMETERS, this.isEnclosingParameters, enclosingParameters);
        this.isEnclosingParameters = enclosingParameters;
        return this;
    }

}
