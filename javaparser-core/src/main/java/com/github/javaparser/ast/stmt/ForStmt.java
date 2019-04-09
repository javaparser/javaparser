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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.ForStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Generated;

/**
 * <h1>The classic for statement</h1>
 * Examples:
 * <ol>
 * <li><code>for(int a=3, b=5; a<99; a++, b++) hello();</code></li>
 * <li><code>for(a=3, b=5; a<99; a++) { hello(); }</code> </li>
 * <li><code>for(a(),b();;) hello();</code> </li>
 * </ol>
 * <ul>
 * <li><i>initialization</i> is a list of expressions.
 * These can be any kind of expression as can be seen in example 3,
 * but the common ones are a single VariableDeclarationExpr (which declares multiple variables) in example 1,
 * or a list of AssignExpr's in example 2.</li>
 * <li><i>compare</i> is an expression,
 * in example 1 and 2 it is a BinaryExpr.
 * In example 3 there is no expression, it is empty.</li>
 * <li><i>update</i> is a list of expressions,
 * in example 1 and 2 they are UnaryExpr's.
 * In example 3 there is no expression, the list empty.</li>
 * <li><i>body</i> is a statement,
 * in example 1 and 3 it is an ExpressionStmt.
 * in example 2 it is a BlockStmt.</li>
 * </ul>
 *
 * @author Julio Vilmar Gesser
 * @see com.github.javaparser.ast.expr.VariableDeclarationExpr
 */
public class ForStmt extends Statement implements NodeWithBody<ForStmt> {

    private NodeList<Expression> initialization;

    @OptionalProperty
    private Expression compare;

    private NodeList<Expression> update;

    private Statement body;

    public ForStmt() {
        this(null, new NodeList<>(), new BooleanLiteralExpr(), new NodeList<>(), new ReturnStmt());
    }

    @AllFieldsConstructor
    public ForStmt(final NodeList<Expression> initialization, final Expression compare, final NodeList<Expression> update, final Statement body) {
        this(null, initialization, compare, update, body);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ForStmt(TokenRange tokenRange, NodeList<Expression> initialization, Expression compare, NodeList<Expression> update, Statement body) {
        super(tokenRange);
        setInitialization(initialization);
        setCompare(compare);
        setUpdate(update);
        setBody(body);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Statement getBody() {
        return body;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getCompare() {
        return Optional.ofNullable(compare);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getInitialization() {
        return initialization;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getUpdate() {
        return update;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForStmt setBody(final Statement body) {
        assertNotNull(body);
        if (body == this.body) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    /**
     * Sets the compare
     *
     * @param compare the compare, can be null
     * @return this, the ForStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForStmt setCompare(final Expression compare) {
        if (compare == this.compare) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.COMPARE, this.compare, compare);
        if (this.compare != null)
            this.compare.setParentNode(null);
        this.compare = compare;
        setAsParentNodeOf(compare);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForStmt setInitialization(final NodeList<Expression> initialization) {
        assertNotNull(initialization);
        if (initialization == this.initialization) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.INITIALIZATION, this.initialization, initialization);
        if (this.initialization != null)
            this.initialization.setParentNode(null);
        this.initialization = initialization;
        setAsParentNodeOf(initialization);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForStmt setUpdate(final NodeList<Expression> update) {
        assertNotNull(update);
        if (update == this.update) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.UPDATE, this.update, update);
        if (this.update != null)
            this.update.setParentNode(null);
        this.update = update;
        setAsParentNodeOf(update);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (compare != null) {
            if (node == compare) {
                removeCompare();
                return true;
            }
        }
        for (int i = 0; i < initialization.size(); i++) {
            if (initialization.get(i) == node) {
                initialization.remove(i);
                return true;
            }
        }
        for (int i = 0; i < update.size(); i++) {
            if (update.get(i) == node) {
                update.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public ForStmt removeCompare() {
        return setCompare((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ForStmt clone() {
        return (ForStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ForStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.forStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == body) {
            setBody((Statement) replacementNode);
            return true;
        }
        if (compare != null) {
            if (node == compare) {
                setCompare((Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < initialization.size(); i++) {
            if (initialization.get(i) == node) {
                initialization.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < update.size(); i++) {
            if (update.get(i) == node) {
                update.set(i, (Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isForStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ForStmt asForStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifForStmt(Consumer<ForStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ForStmt> toForStmt() {
        return Optional.of(this);
    }
}
