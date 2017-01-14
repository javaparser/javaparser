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

package com.github.javaparser.printer;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.observer.ObservableProperty;

import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.ast.observer.ObservableProperty.TYPE;

/**
 * The Concrete Syntax Model for a single node type. It knows the syntax used to represent a certain element in Java
 * code.
 */
public class ConcreteSyntaxModel {

    List<Element> elements;

    interface Element {
        void prettyPrint(Node node, SourcePrinter printer);
    }

    private static class StringElement implements Element {
        private int tokenType;
        private String content;

        public StringElement(int tokenType, String content) {
            this.tokenType = tokenType;
            this.content = content;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            printer.print(content);
        }
    }

    private static class ChildElement implements Element {
        private ObservableProperty property;

        public ChildElement(ObservableProperty property) {
            this.property = property;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            Node child = property.singleValueFor(node);
            if (child != null) {
                genericPrettyPrint(child, printer);
            }
        }
    }

    private static class ListElement implements Element {
        private ObservableProperty property;
        private StringElement separator;

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            throw new UnsupportedOperationException();
        }
    }

    private static class CommentElement implements Element {
        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            if (node.hasComment()) {
                genericPrettyPrint(node.getComment(), printer);
            }
        }
    }

    public List<Element> getElements() {
        throw new UnsupportedOperationException();
    }

    private ConcreteSyntaxModel() {

    }

    public void prettyPrint(Node node, SourcePrinter printer) {
        elements.forEach(e -> e.prettyPrint(node, printer));
    }

    private static class Builder {
        List<Element> elements = new LinkedList<>();

        Builder add(Element e) {
            elements.add(e);
            return this;
        }

        Builder comment() {
            return add(new CommentElement());
        }

        Builder child(ObservableProperty property) {
            return add(new ChildElement(property));
        }

        Builder string(int tokenType, String content) {
            return add(new StringElement(tokenType, content));
        }

        Builder string(int tokenType) {
            return string(tokenType, ASTParserConstants.tokenImage[tokenType]);
        }

        ConcreteSyntaxModel build() {
            ConcreteSyntaxModel instance = new ConcreteSyntaxModel();
            instance.elements = this.elements;
            return instance;
        }
    }

    public static void genericPrettyPrint(Node node, SourcePrinter printer) {
        forClass(node.getClass()).prettyPrint(node, printer);
    }

    public static ConcreteSyntaxModel forClass(Class<? extends Node> nodeClazz) {

        if (nodeClazz.equals(ClassExpr.class)) {
            return new Builder().comment().child(TYPE)
                    .string(ASTParserConstants.DOT)
                    .string(ASTParserConstants.CLASS)
                    .build();
        }

//        @Override
//        public void visit(final ClassExpr n, final Void arg) {
//            printJavaComment(n.getComment(), arg);
//            n.getType().accept(this, arg);
//            printer.print(".class");
//        }

        throw new UnsupportedOperationException();
    }

}
