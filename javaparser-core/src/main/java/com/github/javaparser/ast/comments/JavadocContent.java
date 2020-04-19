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
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.assertNotNull;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavadocContentMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * A JavaDoc content node.
 *
 * @author Simon Sirak
 */
public class JavadocContent extends Comment {

    private JavadocDescription description;

    private NodeList<JavadocBlockTag> blockTags;

    public JavadocContent() {
        this("", new JavadocDescription(), new NodeList<JavadocBlockTag>());
    }

    public JavadocContent(JavadocDescription description, NodeList<JavadocBlockTag> blockTags) {
        this("", description, blockTags);
    }

    @AllFieldsConstructor
    public JavadocContent(String content, JavadocDescription description, NodeList<JavadocBlockTag> blockTags) {
        this(null, content, description, blockTags);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JavadocContent(TokenRange tokenRange, String content, JavadocDescription description, NodeList<JavadocBlockTag> blockTags) {
        super(tokenRange, content);
        setDescription(description);
        setBlockTags(blockTags);
        customInitialization();
    }

    protected JavadocContent(TokenRange tokenRange) {
        super(tokenRange, "");
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocContent setDescription(final JavadocDescription description) {
        assertNotNull(description);
        if (description == this.description) {
            return (JavadocContent) this;
        }
        notifyPropertyChange(ObservableProperty.DESCRIPTION, this.description, description);
        if (this.description != null)
            this.description.setParentNode(null);
        this.description = description;
        setAsParentNodeOf(description);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocContent setBlockTags(final NodeList<JavadocBlockTag> blockTags) {
        assertNotNull(blockTags);
        if (blockTags == this.blockTags) {
            return (JavadocContent) this;
        }
        notifyPropertyChange(ObservableProperty.BLOCK_TAGS, this.blockTags, blockTags);
        if (this.blockTags != null)
            this.blockTags.setParentNode(null);
        this.blockTags = blockTags;
        setAsParentNodeOf(blockTags);
        return this;
    }

    public void addBlockTag(JavadocBlockTag blockTag) {
        if (blockTags == null) {
            blockTags = new NodeList<JavadocBlockTag>();
        }
        blockTags.add(blockTag);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JavadocBlockTag> getBlockTags() {
        return blockTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JavadocDescription getDescription() {
        return description;
    }

    /**
     * Return the text content of the document. It does not contain trailing spaces or asterisks
     * at the start of the line.
     */
    public String toText() {
        StringBuilder sb = new StringBuilder();
        if (!description.toText().isEmpty()) {
            sb.append(description.toText());
            sb.append(EOL);
        }
        if (!blockTags.isEmpty()) {
            sb.append(EOL);
        }
        blockTags.forEach(bt -> {
            sb.append(bt.toText());
            sb.append(EOL);
        });
        return sb.toString();
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJavadocContent() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JavadocContent asJavadocContent() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JavadocContent> toJavadocContent() {
        return Optional.of(this);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJavadocContent(Consumer<JavadocContent> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < blockTags.size(); i++) {
            if (blockTags.get(i) == node) {
                blockTags.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < blockTags.size(); i++) {
            if (blockTags.get(i) == node) {
                blockTags.set(i, (JavadocBlockTag) replacementNode);
                return true;
            }
        }
        if (node == description) {
            setDescription((JavadocDescription) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JavadocContent clone() {
        return (JavadocContent) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JavadocContentMetaModel getMetaModel() {
        return JavaParserMetaModel.javadocContentMetaModel;
    }
}
