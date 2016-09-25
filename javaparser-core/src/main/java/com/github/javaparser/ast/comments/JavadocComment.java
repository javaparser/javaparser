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

import com.github.javaparser.Range;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.HashMap;
import java.util.LinkedList;

/**
 * @author Julio Vilmar Gesser
 */
public final class JavadocComment extends Comment {

    LinkedList<AnnotationPairs> annotations = new LinkedList<>();
    String text;

    public JavadocComment() {
    }

    public JavadocComment(String content) {
        super(content);
    }

    public JavadocComment(Range range, String content) {
        super(range, content);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public String getText() {
        String text = toString();
        text = text.replaceFirst("/\\*\\*\n", "");
        text = text.replaceAll("\n *\\*/.*\n", "");
        text = text.replaceAll(" *\\* *", "");
        this.text = text;
        return text;
    }

    private class AnnotationPairs {
        String annotation;
        String text;

        public AnnotationPairs(String annotation, String text) {
            this.annotation = annotation;
            this.text = text;
        }

        public String getAnnotation() {return annotation;}

        public String getText() {return text;}
    }
}
