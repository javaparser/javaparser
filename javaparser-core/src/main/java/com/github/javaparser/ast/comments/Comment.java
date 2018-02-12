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
package com.github.javaparser.ast.comments;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.CommentMetaModel;
import com.github.javaparser.metamodel.InternalProperty;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Abstract class for all AST nodes that represent comments.
 *
 * @author Julio Vilmar Gesser
 * @see BlockComment
 * @see LineComment
 * @see JavadocComment
 */
public abstract class Comment extends Node {

    private String content;

    @InternalProperty
    private Node commentedNode;

    @AllFieldsConstructor
    public Comment(String content) {
        this(null, content);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public Comment(TokenRange tokenRange, String content) {
        super(tokenRange);
        setContent(content);
        customInitialization();
    }

    /**
     * Return the text of the comment.
     *
     * @return text of the comment
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public String getContent() {
        return content;
    }

    /**
     * Sets the text of the comment.
     *
     * @param content the text of the comment to set
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Comment setContent(final String content) {
        assertNotNull(content);
        if (content == this.content) {
            return (Comment) this;
        }
        notifyPropertyChange(ObservableProperty.CONTENT, this.content, content);
        this.content = content;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLineComment() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LineComment asLineComment() {
        throw new IllegalStateException(f("%s is not an LineComment", this));
    }

    public Optional<Node> getCommentedNode() {
        return Optional.ofNullable(this.commentedNode);
    }

    /**
     * Sets the commentedNode
     *
     * @param commentedNode the commentedNode, can be null
     * @return this, the Comment
     */
    public Comment setCommentedNode(Node commentedNode) {
        notifyPropertyChange(ObservableProperty.COMMENTED_NODE, this.commentedNode, commentedNode);
        if (commentedNode == null) {
            this.commentedNode = null;
            return this;
        }
        if (commentedNode == this) {
            throw new IllegalArgumentException();
        }
        if (commentedNode instanceof Comment) {
            throw new IllegalArgumentException();
        }
        this.commentedNode = commentedNode;
        return this;
    }

    public boolean isOrphan() {
        return this.commentedNode == null;
    }

    @Override
    public boolean remove() {
        // the other are orphan comments and remove should work with them
        if (this.commentedNode != null) {
            this.commentedNode.setComment(null);
            return true;
        } else if (this.getParentNode().isPresent()) {
            return this.getParentNode().get().removeOrphanComment(this);
        } else {
            return false;
        }
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public Comment clone() {
        return (Comment) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public CommentMetaModel getMetaModel() {
        return JavaParserMetaModel.commentMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBlockComment() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BlockComment asBlockComment() {
        throw new IllegalStateException(f("%s is not an BlockComment", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJavadocComment() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JavadocComment asJavadocComment() {
        throw new IllegalStateException(f("%s is not an JavadocComment", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBlockComment(Consumer<BlockComment> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJavadocComment(Consumer<JavadocComment> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLineComment(Consumer<LineComment> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BlockComment> toBlockComment() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JavadocComment> toJavadocComment() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LineComment> toLineComment() {
        return Optional.empty();
    }
}
