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
import com.github.javaparser.metamodel.JavadocSnippetMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * A JavadocSnippet node containing string content.
 *
 * @author Simon Sirak & David Johansson
 */
public class JavadocSnippet extends JavadocDescriptionElement {

    private String text;

    public JavadocSnippet() {
        this(null, "");
    }

    @AllFieldsConstructor
    public JavadocSnippet(String text) {
        this(null, text);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JavadocSnippet(TokenRange tokenRange, String text) {
        super(tokenRange);
        setText(text);
        customInitialization();
    }

    /**
     * Set text of current node.
     *
     * @param text string text
     * @return new version of current object
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocSnippet setText(final String text) {
        assertNotNull(text);
        if (text == this.text) {
            return (JavadocSnippet) this;
        }
        notifyPropertyChange(ObservableProperty.TEXT, this.text, text);
        this.text = text;
        return this;
    }

    /**
     * Return the text content of the the snippet.
     *
     * @return string content
     */
    public String toText() {
        return text;
    }

    /**
     * Return the text content of the the snippet.
     *
     * @return string content
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public String getText() {
        return text;
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
    public JavadocSnippet clone() {
        return (JavadocSnippet) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JavadocSnippetMetaModel getMetaModel() {
        return JavaParserMetaModel.javadocSnippetMetaModel;
    }
}
