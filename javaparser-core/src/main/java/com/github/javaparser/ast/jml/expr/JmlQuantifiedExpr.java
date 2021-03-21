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
package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlBindingExprMetaModel;
import com.github.javaparser.metamodel.NonEmptyProperty;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.metamodel.JmlQuantifiedExprMetaModel;

/**
 * 12.4.24.2 Generalized Quantifiers
 * https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC163
 *
 * @author Alexander Weigl
 */
public class JmlQuantifiedExpr extends Expression {

    /**
     * 12.4.24.2 Generalized Quantifiers
     */
    public enum JmlBinder {

        FORALL("\\forall"),
        EXISTS("\\exists"),
        NUM_OF("\\num_of"),
        MIN("\\min"),
        MAX("\\max"),
        SUM("\\sum"),
        PRODUCT("\\product");

        public final String symbol;

        JmlBinder(String symbol) {
            this.symbol = symbol;
        }
    }

    private JmlBinder binder;

    @NonEmptyProperty
    private NodeList<VariableDeclarator> variables;

    @NonEmptyProperty
    private NodeList<Expression> expressions;

    public JmlQuantifiedExpr() {
        this(null, JmlBinder.EXISTS, new NodeList<>(), new NodeList<>());
    }

    public JmlQuantifiedExpr(final NodeList<VariableDeclarator> variables, final Expression expressions) {
        this(null, JmlBinder.EXISTS, variables, new NodeList<>(expressions));
    }

    @AllFieldsConstructor
    public JmlQuantifiedExpr(final JmlBinder binder, final NodeList<VariableDeclarator> variables, final Expression expressions) {
        this(null, binder, variables, new NodeList<>(expressions));
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlQuantifiedExpr(TokenRange tokenRange, JmlBinder binder, NodeList<VariableDeclarator> variables, NodeList<Expression> expressions) {
        super(tokenRange);
        setBinder(binder);
        setVariables(variables);
        setExpressions(expressions);
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
    public boolean isJmlBindingExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlQuantifiedExpr asJmlBindingExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlQuantifiedExpr> toJmlBindingExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlBindingExpr(Consumer<JmlQuantifiedExpr> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExpressions() {
        return expressions;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlQuantifiedExpr setExpressions(final NodeList<Expression> expressions) {
        assertNotNull(expressions);
        if (expressions == this.expressions) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSIONS, this.expressions, expressions);
        if (this.expressions != null)
            this.expressions.setParentNode(null);
        this.expressions = expressions;
        setAsParentNodeOf(expressions);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<VariableDeclarator> getVariables() {
        return variables;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlQuantifiedExpr setVariables(final NodeList<VariableDeclarator> variables) {
        assertNotNull(variables);
        if (variables == this.variables) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.VARIABLES, this.variables, variables);
        if (this.variables != null)
            this.variables.setParentNode(null);
        this.variables = variables;
        setAsParentNodeOf(variables);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.remove(i);
                return true;
            }
        }
        for (int i = 0; i < variables.size(); i++) {
            if (variables.get(i) == node) {
                variables.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < variables.size(); i++) {
            if (variables.get(i) == node) {
                variables.set(i, (VariableDeclarator) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlQuantifiedExpr clone() {
        return (JmlQuantifiedExpr) accept(new CloneVisitor(), null);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlBinder getBinder() {
        return binder;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlQuantifiedExpr setBinder(final JmlBinder binder) {
        assertNotNull(binder);
        if (binder == this.binder) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BINDER, this.binder, binder);
        this.binder = binder;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlQuantifiedExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlQuantifiedExpr asJmlQuantifiedExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlQuantifiedExpr> toJmlQuantifiedExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlQuantifiedExpr(Consumer<JmlQuantifiedExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlQuantifiedExprMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlQuantifiedExprMetaModel;
    }
}
