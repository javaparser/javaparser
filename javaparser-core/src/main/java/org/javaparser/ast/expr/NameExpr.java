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
import org.javaparser.ast.nodeTypes.NodeWithSimpleName;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.NameExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import org.javaparser.resolution.Resolvable;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

/**
 * Whenever a SimpleName is used in an expression, it is wrapped in NameExpr.
 * <br/>In <code>int x = a + 3;</code> a is a SimpleName inside a NameExpr.
 *
 * @author Julio Vilmar Gesser
 */
public class NameExpr extends Expression implements NodeWithSimpleName<NameExpr>, Resolvable<ResolvedValueDeclaration> {

    private SimpleName name;

    public NameExpr() {
        this(null, new SimpleName());
    }

    public NameExpr(final String name) {
        this(null, new SimpleName(name));
    }

    @AllFieldsConstructor
    public NameExpr(final SimpleName name) {
        this(name.getTokenRange().orElse(null), name);
        setRange(name.getRange().orElse(null));
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public NameExpr(TokenRange tokenRange, SimpleName name) {
        super(tokenRange);
        setName(name);
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
    public SimpleName getName() {
        return name;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NameExpr setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return (NameExpr) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
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
    public NameExpr clone() {
        return (NameExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public NameExprMetaModel getMetaModel() {
        return JavaParserMetaModel.nameExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isNameExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public NameExpr asNameExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifNameExpr(Consumer<NameExpr> action) {
        action.accept(this);
    }

    /**
     * Attempts to resolve the declaration corresponding to the accessed name. If successful, a
     * {@link ResolvedValueDeclaration} representing the declaration of the value accessed by this {@code NameExpr} is
     * returned. Otherwise, an {@link UnsolvedSymbolException} is thrown.
     *
     * @return a {@link ResolvedValueDeclaration} representing the declaration of the accessed value.
     * @throws UnsolvedSymbolException if the declaration corresponding to the name expression could not be resolved.
     * @see FieldAccessExpr#resolve()
     * @see MethodCallExpr#resolve()
     * @see ObjectCreationExpr#resolve()
     * @see ExplicitConstructorInvocationStmt#resolve()
     */
    @Override
    public ResolvedValueDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedValueDeclaration.class);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<NameExpr> toNameExpr() {
        return Optional.of(this);
    }
}
