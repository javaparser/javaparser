/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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
package com.github.javaparser.ast.comments;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavadocBlockTagMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A JavaDoc block tag. Different tag types are defined by the BlockTagType enum.
 *
 * @author Simon Sirak & David Johansson
 */
public class JavadocBlockTag extends Node {

    private JavadocDescription description;

    private BlockTagType type;

    public enum BlockTagType {

        AUTHOR,
        DEPRECATED,
        EXCEPTION,
        PARAM,
        RETURN,
        SEE,
        SERIAL,
        SERIAL_DATA,
        SERIAL_FIELD,
        SINCE,
        THROWS,
        VERSION,
        UNKNOWN;

        public String toString() {
            return this.name().toLowerCase();
        }
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JavadocBlockTag(TokenRange tokenRange, JavadocDescription description, BlockTagType type) {
        super(tokenRange);
        setDescription(description);
        setType(type);
        customInitialization();
    }

    public JavadocBlockTag() {
        this(null, new JavadocDescription(), BlockTagType.UNKNOWN);
    }

    @AllFieldsConstructor
    public JavadocBlockTag(JavadocDescription description, BlockTagType type) {
        this(null, description, type);
    }

    // TODO: Use optional instead of null check ?
    public String toText() {
        StringBuilder sb = new StringBuilder();
        sb.append("@");
        sb.append(type.toString());
        if (!description.toText().isEmpty()) {
            sb.append(" ");
            sb.append(description.toText());
        }
        return sb.toString();
    }

    /**
     * Set the description of the block tag.
     *
     * @param description describes the tag
     * @return new version of current object
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocBlockTag setDescription(final JavadocDescription description) {
        assertNotNull(description);
        if (description == this.description) {
            return (JavadocBlockTag) this;
        }
        notifyPropertyChange(ObservableProperty.DESCRIPTION, this.description, description);
        if (this.description != null)
            this.description.setParentNode(null);
        this.description = description;
        setAsParentNodeOf(description);
        return this;
    }

    /**
     * Set the type of the block tag.
     *
     * @param type the block tag type
     * @return new version of current object
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocBlockTag setType(final BlockTagType type) {
        assertNotNull(type);
        if (type == this.type) {
            return (JavadocBlockTag) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        return this;
    }

    /**
     * Gets the description associated with the tag.
     *
     * @return tag description
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocDescription getDescription() {
        return description;
    }

    /**
     * Gets the type associated with the tag.
     *
     * @return tag type
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BlockTagType getType() {
        return type;
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
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == description) {
            setDescription((JavadocDescription) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JavadocBlockTag clone() {
        return (JavadocBlockTag) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JavadocBlockTagMetaModel getMetaModel() {
        return JavaParserMetaModel.javadocBlockTagMetaModel;
    }
}
