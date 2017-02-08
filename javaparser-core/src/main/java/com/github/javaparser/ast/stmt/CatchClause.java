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
package com.github.javaparser.ast.stmt;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.EnumSet;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;

/**
 * The catch part of a try-catch-finally. <br/>In <code>try { ... } catch (Exception e) { ... }</code> the CatchClause
 * is <code>catch (Exception e) { ... }</code>. Exception e is the parameter. The { ... } is the body.
 *
 * @author Julio Vilmar Gesser
 */
public final class CatchClause extends Node implements NodeWithBlockStmt<CatchClause> {

    private Parameter parameter;

    private BlockStmt body;

    public CatchClause() {
        this(null, new Parameter(), new BlockStmt());
    }

    public CatchClause(final EnumSet<Modifier> exceptModifier, final NodeList<AnnotationExpr> exceptAnnotations, final ClassOrInterfaceType exceptType, final SimpleName exceptName, final BlockStmt body) {
        this(null, new Parameter(null, exceptModifier, exceptAnnotations, exceptType, false, exceptName), body);
    }

    @AllFieldsConstructor
    public CatchClause(final Parameter parameter, final BlockStmt body) {
        this(null, parameter, body);
    }

    public CatchClause(final Range range, final Parameter parameter, final BlockStmt body) {
        super(range);
        setParameter(parameter);
        setBody(body);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * Note that the type of the Parameter can be a UnionType. In this case, any annotations found at the start of the
     * catch(@X A a |...) are found directly in the Parameter. Annotations that are on the second or later type -
     * catch(A a | @X B b ...) are found on those types.
     */
    public Parameter getParameter() {
        return parameter;
    }

    public CatchClause setParameter(final Parameter parameter) {
        assertNotNull(parameter);
        notifyPropertyChange(ObservableProperty.PARAMETER, this.parameter, parameter);
        if (this.parameter != null)
            this.parameter.setParentNode(null);
        this.parameter = parameter;
        setAsParentNodeOf(parameter);
        return this;
    }

    @Override
    public BlockStmt getBody() {
        return body;
    }

    @Override
    public CatchClause setBody(final BlockStmt body) {
        assertNotNull(body);
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public CatchClause clone() {
        return (CatchClause) accept(new CloneVisitor(), null);
    }
}

