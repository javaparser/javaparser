/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.NonEmptyProperty;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlBindingExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * <h1>A lambda expression</h1>
 * <h2>Java 1-7</h2>
 * Does not exist.
 * <h2>Java 8+</h2>
 * {@code (a, b) -> a + b}
 * <br>{@code a -> ...}
 * <br>{@code (Long a) -> { println(a); }}
 * <p>The parameters are on the left side of the -&gt;.
 * If a parameter uses type inference (it has no type specified) then its type is set to {@code UnknownType}.
 * If they are in ( ), "isEnclosingParameters" is true.
 * <br>The body is to the right of the -&gt;.
 * The body is either a BlockStmt when it is in { } braces, or an ExpressionStmt when it is not in braces.
 *
 * @author Raquel Pau
 */
public class JmlBindingExpr extends Expression {

    @NonEmptyProperty
    private NodeList<VariableDeclarator> variables;

    private NodeList<Expression> body;

    public JmlBindingExpr() {
        this(null, new NodeList<>(), new NodeList<>());
    }

    /**
     * Creates a single parameter lambda expression.
     */
    public JmlBindingExpr(VariableDeclarator var, Expression body) {
        this(null, new NodeList<>(var), new NodeList<>(body));
    }

    /**
     * Creates a zero or multi-parameter lambda expression with its variables wrapped in ( ).
     */
    @AllFieldsConstructor
    public JmlBindingExpr(NodeList<VariableDeclarator> variables, Expression body) {
        this(null, variables, new NodeList<>(body));
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlBindingExpr(TokenRange tokenRange, NodeList<VariableDeclarator> variables, NodeList<Expression> body) {
        super(tokenRange);
        this.variables = variables;
        this.body = body;
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLambdaExpr() {
        return true;
    }

    /*
     * Lambda expressions are always poly expressions
     */
    @Override
    public boolean isPolyExpression() {
        return true;
    }

    @Override
    public boolean isJmlBindingExpr() {
        return true;
    }

    @Override
    public JmlBindingExpr asJmlBindingExpr() {
        return this;
    }

    @Override
    public Optional<JmlBindingExpr> toJmlBindingExpr() {
        return Optional.of(this);
    }

    public void ifJmlBindingExpr(Consumer<JmlBindingExpr> action) {
        action.accept(this);
    }

    public Statement getBody() {
        return body;
    }

    public JmlBindingExpr setBody(final Statement body) {
        assertNotNull(body);
        if (body == this.body) {
            return (JmlBindingExpr) this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    public boolean isEnclosingParameters() {
        return isEnclosingParameters;
    }

    public JmlBindingExpr setEnclosingParameters(final boolean isEnclosingParameters) {
        if (isEnclosingParameters == this.isEnclosingParameters) {
            return (JmlBindingExpr) this;
        }
        notifyPropertyChange(ObservableProperty.ENCLOSING_PARAMETERS, this.isEnclosingParameters, isEnclosingParameters);
        this.isEnclosingParameters = isEnclosingParameters;
        return this;
    }

    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    public JmlBindingExpr setParameters(final NodeList<Parameter> parameters) {
        assertNotNull(parameters);
        if (parameters == this.parameters) {
            return (JmlBindingExpr) this;
        }
        notifyPropertyChange(ObservableProperty.PARAMETERS, this.parameters, parameters);
        if (this.parameters != null)
            this.parameters.setParentNode(null);
        this.parameters = parameters;
        setAsParentNodeOf(parameters);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < parameters.size(); i++) {
            if (parameters.get(i) == node) {
                parameters.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == body) {
            setBody((Statement) replacementNode);
            return true;
        }
        for (int i = 0; i < parameters.size(); i++) {
            if (parameters.get(i) == node) {
                parameters.set(i, (Parameter) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public JmlBindingExpr clone() {
        return (JmlBindingExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlBindingExprMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlBindingExprMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlBindingExpr(TokenRange tokenRange, NodeList<Parameter> parameters, Statement body, boolean isEnclosingParameters) {
        super(tokenRange);
        setParameters(parameters);
        setBody(body);
        setEnclosingParameters(isEnclosingParameters);
        customInitialization();
    }
}
