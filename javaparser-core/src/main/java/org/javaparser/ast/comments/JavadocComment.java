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
package org.javaparser.ast.comments;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import org.javaparser.javadoc.Javadoc;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.JavadocCommentMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;
import static org.javaparser.StaticJavaParser.parseJavadoc;

/**
 * A Javadoc comment. <code>/&#42;&#42; a comment &#42;/</code>
 *
 * @author Julio Vilmar Gesser
 */
public class JavadocComment extends Comment {

    public JavadocComment() {
        this(null, "empty");
    }

    @AllFieldsConstructor
    public JavadocComment(String content) {
        this(null, content);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public JavadocComment(TokenRange tokenRange, String content) {
        super(tokenRange, content);
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

    public Javadoc parse() {
        return parseJavadoc(getContent());
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
    public JavadocComment clone() {
        return (JavadocComment) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public JavadocCommentMetaModel getMetaModel() {
        return JavaParserMetaModel.javadocCommentMetaModel;
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
    public boolean isJavadocComment() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public JavadocComment asJavadocComment() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJavadocComment(Consumer<JavadocComment> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JavadocComment> toJavadocComment() {
        return Optional.of(this);
    }
}
