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

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.nodeTypes.NodeWithCondition;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.DoStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import com.github.javaparser.ast.Generated;

/**
 * A do-while.
 * <br/><code>do { ... } while ( a==0 );</code>
 *
 * @author Julio Vilmar Gesser
 */
public class DoStmt extends Statement implements NodeWithBody<DoStmt>, NodeWithCondition<DoStmt> {

    private Statement body;

    private Expression condition;

    public DoStmt() {
        this(null, new ReturnStmt(), new BooleanLiteralExpr());
    }

    @AllFieldsConstructor
    public DoStmt(final Statement body, final Expression condition) {
        this(null, body, condition);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public DoStmt(TokenRange tokenRange, Statement body, Expression condition) {
        super(tokenRange);
        setBody(body);
        setCondition(condition);
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
    public Expression getCondition() {
        return condition;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public DoStmt setBody(final Statement body) {
        assertNotNull(body);
        if (body == this.body) {
            return (DoStmt) this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public DoStmt setCondition(final Expression condition) {
        assertNotNull(condition);
        if (condition == this.condition) {
            return (DoStmt) this;
        }
        notifyPropertyChange(ObservableProperty.CONDITION, this.condition, condition);
        if (this.condition != null)
            this.condition.setParentNode(null);
        this.condition = condition;
        setAsParentNodeOf(condition);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public DoStmt clone() {
        return (DoStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public DoStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.doStmtMetaModel;
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
        if (node == condition) {
            setCondition((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isDoStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public DoStmt asDoStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifDoStmt(Consumer<DoStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<DoStmt> toDoStmt() {
        return Optional.of(this);
    }
}
