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
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import org.javaparser.metamodel.DoubleLiteralExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

/**
 * A float or a double constant. This value is stored exactly as found in the source.
 * <br/><code>100.1f</code>
 * <br/><code>23958D</code>
 * <br/><code>0x4.5p1f</code>
 *
 * @author Julio Vilmar Gesser
 */
public class DoubleLiteralExpr extends LiteralStringValueExpr {

    public DoubleLiteralExpr() {
        this(null, "0");
    }

    @AllFieldsConstructor
    public DoubleLiteralExpr(final String value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public DoubleLiteralExpr(TokenRange tokenRange, String value) {
        super(tokenRange, value);
        customInitialization();
    }

    public DoubleLiteralExpr(final double value) {
        this(null, String.valueOf(value));
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

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    /**
     * @return the literal value as a double
     */
    public double asDouble() {
        // Underscores are allowed in number literals for readability reasons but cause a NumberFormatException if
        // passed along to Double#parseDouble. Hence, we apply a simple filter to remove all underscores.
        // See https://github.com/javaparser/javaparser/issues/1980 for more information.
        String noUnderscoreValue = value.replaceAll("_", "");
        return Double.parseDouble(noUnderscoreValue);
    }

    public DoubleLiteralExpr setDouble(double value) {
        this.value = String.valueOf(value);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public DoubleLiteralExpr clone() {
        return (DoubleLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public DoubleLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.doubleLiteralExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isDoubleLiteralExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public DoubleLiteralExpr asDoubleLiteralExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifDoubleLiteralExpr(Consumer<DoubleLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<DoubleLiteralExpr> toDoubleLiteralExpr() {
        return Optional.of(this);
    }
}
