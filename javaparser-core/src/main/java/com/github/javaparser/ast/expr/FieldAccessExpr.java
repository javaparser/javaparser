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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalScope;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.FieldAccessExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;

/**
 * Access of a field of an object.
 * <br/><code>person.name</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class FieldAccessExpr extends Expression implements NodeWithSimpleName<FieldAccessExpr>, NodeWithTypeArguments<FieldAccessExpr>, NodeWithOptionalScope<FieldAccessExpr> {

    private Expression scope;

    private NodeList<Type> typeArguments;

    private SimpleName name;

    public FieldAccessExpr() {
        this(null, new ThisExpr(), new NodeList<>(), new SimpleName());
    }

    public FieldAccessExpr(final Expression scope, final String name) {
        this(null, scope, new NodeList<>(), new SimpleName(name));
    }

    @AllFieldsConstructor
    public FieldAccessExpr(final Expression scope, final NodeList<Type> typeArguments, final SimpleName name) {
        this(null, scope, typeArguments, name);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public FieldAccessExpr(Range range, Expression scope, NodeList<Type> typeArguments, SimpleName name) {
        super(range);
        setScope(scope);
        setTypeArguments(typeArguments);
        setName(name);
        customInitialization();
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    @Override
    public FieldAccessExpr setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return (FieldAccessExpr) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    /**
     * Use {@link #getName} instead.
     */
    @Deprecated
    public SimpleName getField() {
        return name;
    }

    @Override
    public Optional<Expression> getScope() {
        return Optional.ofNullable(scope);
    }

    /**
     * Use {@link #setName} with new SimpleName(field) instead.
     */
    @Deprecated
    public FieldAccessExpr setField(final String field) {
        setName(new SimpleName(field));
        return this;
    }

    /**
     * Use {@link #setName} instead.
     */
    @Deprecated
    public FieldAccessExpr setFieldExpr(SimpleName inner) {
        return setName(inner);
    }

    /**
     * Sets the scope
     *
     * @param scope the scope, can be null
     * @return this, the FieldAccessExpr
     */
    @Override
    public FieldAccessExpr setScope(final Expression scope) {
        if (scope == this.scope) {
            return (FieldAccessExpr) this;
        }
        notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        if (this.scope != null)
            this.scope.setParentNode(null);
        this.scope = scope;
        setAsParentNodeOf(scope);
        return this;
    }

    @Override
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the type arguments
     *
     * @param types the type arguments, can be null
     * @return this, the FieldAccessExpr
     */
    @Override
    public FieldAccessExpr setTypeArguments(final NodeList<Type> typeArguments) {
        if (typeArguments == this.typeArguments) {
            return (FieldAccessExpr) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        if (this.typeArguments != null)
            this.typeArguments.setParentNode(null);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(typeArguments);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getTypeArguments().orElse(null));
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (scope != null) {
            if (node == scope) {
                removeScope();
                return true;
            }
        }
        if (typeArguments != null) {
            for (int i = 0; i < typeArguments.size(); i++) {
                if (typeArguments.get(i) == node) {
                    typeArguments.remove(i);
                    return true;
                }
            }
        }
        return super.remove(node);
    }

    public FieldAccessExpr removeScope() {
        return setScope((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public FieldAccessExpr clone() {
        return (FieldAccessExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public FieldAccessExprMetaModel getMetaModel() {
        return JavaParserMetaModel.fieldAccessExprMetaModel;
    }
}
