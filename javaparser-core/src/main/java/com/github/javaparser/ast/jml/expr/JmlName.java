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
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithIdentifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.NonEmptyProperty;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNonEmpty;
import com.github.javaparser.metamodel.JmlNameMetaModel;

/**
 * A name that may consist of multiple identifiers.
 * In other words: it.may.contain.dots.
 * <p>
 * The rightmost identifier is "identifier",
 * The one to the left of it is "qualifier.identifier", etc.
 * <p>
 * You can construct one from a String with the name(...) method.
 *
 * @author Julio Vilmar Gesser
 * @see SimpleName
 */
public class JmlName extends Node implements NodeWithIdentifier<JmlName>, Jmlish {

    @NonEmptyProperty
    private String identifier;

    @OptionalProperty
    private JmlName qualifier;

    public JmlName() {
        this(null, "empty");
    }

    @AllFieldsConstructor
    public JmlName(final String identifier) {
        this(null, identifier);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlName(TokenRange tokenRange, String identifier) {
        super(tokenRange);
        setIdentifier(identifier);
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
    public String getIdentifier() {
        return identifier;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlName setIdentifier(final String identifier) {
        assertNonEmpty(identifier);
        if (identifier == this.identifier) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.IDENTIFIER, this.identifier, identifier);
        this.identifier = identifier;
        return this;
    }

    /**
     * @return the complete qualified name. Only the identifiers and the dots, so no comments or whitespace.
     */
    public String asString() {
        if (qualifier != null) {
            return qualifier.asString() + "." + identifier;
        }
        return identifier;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<JmlName> getQualifier() {
        return Optional.ofNullable(qualifier);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlName setQualifier(final JmlName qualifier) {
        if (qualifier == this.qualifier) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.QUALIFIER, this.qualifier, qualifier);
        if (this.qualifier != null)
            this.qualifier.setParentNode(null);
        this.qualifier = qualifier;
        setAsParentNodeOf(qualifier);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (qualifier != null) {
            if (node == qualifier) {
                removeQualifier();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlName removeQualifier() {
        return setQualifier(null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlName clone() {
        return (JmlName) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlNameMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlNameMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (qualifier != null) {
            if (node == qualifier) {
                setQualifier((JmlName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    /**
     * A top level name is a name that is not contained in a larger Name instance.
     */
    public boolean isTopLevel() {
        return !isInternal();
    }

    /**
     * An internal name is a name that constitutes a part of a larger Name instance.
     */
    public boolean isInternal() {
        return getParentNode().filter(parent -> parent instanceof JmlName).isPresent();
    }
}
