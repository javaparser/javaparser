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
package org.javaparser.ast.expr;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.nodeTypes.NodeWithExpression;
import org.javaparser.ast.nodeTypes.NodeWithType;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.type.ClassOrInterfaceType;
import org.javaparser.ast.type.ReferenceType;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.InstanceOfExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

/**
 * Usage of the instanceof operator.
 * <br/><code>tool instanceof Drill</code>
 *
 * @author Julio Vilmar Gesser
 */
public class InstanceOfExpr extends Expression implements NodeWithType<InstanceOfExpr, ReferenceType>, NodeWithExpression<InstanceOfExpr> {

    private Expression expression;

    private ReferenceType type;

    public InstanceOfExpr() {
        this(null, new NameExpr(), new ClassOrInterfaceType());
    }

    @AllFieldsConstructor
    public InstanceOfExpr(final Expression expression, final ReferenceType type) {
        this(null, expression, type);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public InstanceOfExpr(TokenRange tokenRange, Expression expression, ReferenceType type) {
        super(tokenRange);
        setExpression(expression);
        setType(type);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ReferenceType getType() {
        return type;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public InstanceOfExpr setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return (InstanceOfExpr) this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public InstanceOfExpr setType(final ReferenceType type) {
        assertNotNull(type);
        if (type == this.type) {
            return (InstanceOfExpr) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public InstanceOfExpr clone() {
        return (InstanceOfExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public InstanceOfExprMetaModel getMetaModel() {
        return JavaParserMetaModel.instanceOfExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        if (node == type) {
            setType((ReferenceType) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isInstanceOfExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public InstanceOfExpr asInstanceOfExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifInstanceOfExpr(Consumer<InstanceOfExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<InstanceOfExpr> toInstanceOfExpr() {
        return Optional.of(this);
    }
}
