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
package com.github.javaparser.ast.comments;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavadocInlineTagMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * A JavaDoc inlinde tag node.
 *
 * @author Simon Sirak & David Johansson
 */
public class JavadocInlineTag extends JavadocDescriptionElement {

    private InlineTagType type;

    private String content;

    public enum InlineTagType {

        CODE,
        DOC_ROOT,
        INHERIT_DOC,
        LINK,
        LINKPLAIN,
        LITERAL,
        VALUE,
        SYSTEM_PROPERTY,
        UNKNOWN;

        public String toString() {
            return this.name().toLowerCase();
        }
    }

    public JavadocInlineTag() {
        this(null, InlineTagType.UNKNOWN, "");
    }

    @AllFieldsConstructor
    public JavadocInlineTag(InlineTagType type, String content) {
        this(null, type, content);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JavadocInlineTag(TokenRange tokenRange, InlineTagType type, String content) {
        super(tokenRange);
        setType(type);
        setContent(content);
        customInitialization();
    }

    /**
     * Set type of inline tag.
     *
     * @param type type of tag
     * @return new version of current object
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocInlineTag setType(final InlineTagType type) {
        assertNotNull(type);
        if (type == this.type) {
            return (JavadocInlineTag) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        return this;
    }

    /**
     * Set content of inline tag.
     *
     * @param type content of tag
     * @return new version of current object
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocInlineTag setContent(final String content) {
        assertNotNull(content);
        if (content == this.content) {
            return (JavadocInlineTag) this;
        }
        notifyPropertyChange(ObservableProperty.CONTENT, this.content, content);
        this.content = content;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public String getContent() {
        return content;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public InlineTagType getType() {
        return type;
    }

    /**
     * Return the text content of the the inline tag.
     *
     * @return string content
     */
    public String toText() {
        return "{@" + type.toString() + content + "}";
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
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JavadocInlineTag clone() {
        return (JavadocInlineTag) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JavadocInlineTagMetaModel getMetaModel() {
        return JavaParserMetaModel.javadocInlineTagMetaModel;
    }
}
