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

import org.javaparser.TokenRange;
import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.nodeTypes.NodeWithIdentifier;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.metamodel.NameMetaModel;
import org.javaparser.metamodel.NonEmptyProperty;
import org.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import static org.javaparser.utils.Utils.assertNonEmpty;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.Generated;

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
public class Name extends Node implements NodeWithIdentifier<Name> {

    @NonEmptyProperty
    private String identifier;

    @OptionalProperty
    private Name qualifier;

    public Name() {
        this(null, null, "empty");
    }

    public Name(final String identifier) {
        this(null, null, identifier);
    }

    @AllFieldsConstructor
    public Name(Name qualifier, final String identifier) {
        this(null, qualifier, identifier);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public Name(TokenRange tokenRange, Name qualifier, String identifier) {
        super(tokenRange);
        setQualifier(qualifier);
        setIdentifier(identifier);
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
    public String getIdentifier() {
        return identifier;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Name setIdentifier(final String identifier) {
        assertNonEmpty(identifier);
        if (identifier == this.identifier) {
            return (Name) this;
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

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Name> getQualifier() {
        return Optional.ofNullable(qualifier);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Name setQualifier(final Name qualifier) {
        if (qualifier == this.qualifier) {
            return (Name) this;
        }
        notifyPropertyChange(ObservableProperty.QUALIFIER, this.qualifier, qualifier);
        if (this.qualifier != null)
            this.qualifier.setParentNode(null);
        this.qualifier = qualifier;
        setAsParentNodeOf(qualifier);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
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

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public Name removeQualifier() {
        return setQualifier((Name) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public Name clone() {
        return (Name) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public NameMetaModel getMetaModel() {
        return JavaParserMetaModel.nameMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (qualifier != null) {
            if (node == qualifier) {
                setQualifier((Name) replacementNode);
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
        return getParentNode().filter(parent -> parent instanceof Name).isPresent();
    }
}
