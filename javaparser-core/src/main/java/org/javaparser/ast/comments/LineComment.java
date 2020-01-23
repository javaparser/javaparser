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
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.LineCommentMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.ast.Generated;

/**
 * <p>
 * AST node that represent line comments.
 * </p>
 * Line comments start with "//" and finish at the end of the line ("\n").
 *
 * @author Julio Vilmar Gesser
 */
public class LineComment extends Comment {

    public LineComment() {
        this(null, "empty");
    }

    @AllFieldsConstructor
    public LineComment(String content) {
        this(null, content);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public LineComment(TokenRange tokenRange, String content) {
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

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLineComment() {
        return true;
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
    public LineComment clone() {
        return (LineComment) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public LineCommentMetaModel getMetaModel() {
        return JavaParserMetaModel.lineCommentMetaModel;
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
    public LineComment asLineComment() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLineComment(Consumer<LineComment> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LineComment> toLineComment() {
        return Optional.of(this);
    }
}
