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
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.ForEachStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A for-each statement.
 * <br/><code>for(Object o: objects) { ... }</code>
 * It was introduced in Java 5.
 *
 * @author Julio Vilmar Gesser
 */
public class ForEachStmt extends Statement implements NodeWithBody<ForEachStmt> {

    private VariableDeclarationExpr variable;

    private Expression iterable;

    private Statement body;

    public ForEachStmt() {
        this(null, new VariableDeclarationExpr(), new NameExpr(), new ReturnStmt());
    }

    @AllFieldsConstructor
    public ForEachStmt(final VariableDeclarationExpr variable, final Expression iterable, final Statement body) {
        this(null, variable, iterable, body);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ForEachStmt(TokenRange tokenRange, VariableDeclarationExpr variable, Expression iterable, Statement body) {
        super(tokenRange);
        setVariable(variable);
        setIterable(iterable);
        setBody(body);
        customInitialization();
    }

    public ForEachStmt(VariableDeclarationExpr variable, String iterable, BlockStmt body) {
        this(null, variable, new NameExpr(iterable), body);
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
    public Expression getIterable() {
        return iterable;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarationExpr getVariable() {
        return variable;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForEachStmt setBody(final Statement body) {
        assertNotNull(body);
        if (body == this.body) {
            return (ForEachStmt) this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForEachStmt setIterable(final Expression iterable) {
        assertNotNull(iterable);
        if (iterable == this.iterable) {
            return (ForEachStmt) this;
        }
        notifyPropertyChange(ObservableProperty.ITERABLE, this.iterable, iterable);
        if (this.iterable != null)
            this.iterable.setParentNode(null);
        this.iterable = iterable;
        setAsParentNodeOf(iterable);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForEachStmt setVariable(final VariableDeclarationExpr variable) {
        assertNotNull(variable);
        if (variable == this.variable) {
            return (ForEachStmt) this;
        }
        notifyPropertyChange(ObservableProperty.VARIABLE, this.variable, variable);
        if (this.variable != null)
            this.variable.setParentNode(null);
        this.variable = variable;
        setAsParentNodeOf(variable);
        return this;
    }

    /**
     * Convenience method that directly returns this foreach statement's single variable declarator.
     * Note that any foreach statement's variable declaration expression (as returned by {@link #getVariable()}) always
     * has exactly one variable declarator.
     * <p>
     * Calling this method on a foreach statement {@code forEachStmt} is equivalent to calling
     * {@code forEachStmt.getVariable().getVariable(0)}.
     *
     * @return this foreach statement's single variable declarator.
     */
    public VariableDeclarator getVariableDeclarator() {
        return getVariable().getVariable(0);
    }

    /**
     * Convenience method that decides whether this foreach statement's variable is {@code final}.
     * Note that any foreach statement's variable declaration expression (as returned by {@link #getVariable()}) always
     * has either no modifiers, or a single {@code final} modifier.
     * <p>
     * Calling this method on a foreach statement {@code forEachStmt} is equivalent to calling
     * {@code forEachStmt.getVariable().getModifiers().isNonEmpty() &&
     * forEachStmt.getVariable().getModifiers().get(0).getKeyword() == Modifier.Keyword.FINAL}.
     *
     * @return {@code true} if this foreach statement's variable is {@code final}, and {@code false} otherwise.
     */
    public boolean hasFinalVariable() {
        return getVariable().getModifiers().isNonEmpty() && getVariable().getModifiers().get(0).getKeyword() == Modifier.Keyword.FINAL;
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
    public ForEachStmt clone() {
        return (ForEachStmt) accept(new CloneVisitor(), null);
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
        if (node == iterable) {
            setIterable((Expression) replacementNode);
            return true;
        }
        if (node == variable) {
            setVariable((VariableDeclarationExpr) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isForEachStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ForEachStmt asForEachStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ForEachStmt> toForEachStmt() {
        return Optional.of(this);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifForEachStmt(Consumer<ForEachStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ForEachStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.forEachStmtMetaModel;
    }
}
