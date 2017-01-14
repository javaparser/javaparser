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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.Observable;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Predicate;

import static com.github.javaparser.ast.observer.ObservableProperty.*;

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
        private ObservableProperty propertyContent;

        public StringElement(int tokenType) {
            this.tokenType = tokenType;
            this.content = ASTParserConstants.tokenImage[tokenType];
            if (content.startsWith("\"")) {
                content = content.substring(1, content.length() - 1);
            }
        }

        public StringElement(int tokenType, String content) {
            this.tokenType = tokenType;
            this.content = content;
        }

        public StringElement(int tokenType, ObservableProperty content) {
            this.tokenType = tokenType;
            this.propertyContent = content;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            if (content != null) {
                printer.print(content);
            } else {
                printer.print(propertyContent.singleStringValueFor(node));
            }
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
        private Element separator;
        private Element preceeding;
        private Element following;

        public ListElement(ObservableProperty property, Element separator) {
            this.property = property;
            this.separator = separator;
        }

        public ListElement(ObservableProperty property) {
            this.property = property;
            this.separator = null;
        }

        public ListElement(ObservableProperty property, Element separator, Element preceeding, Element following) {
            this.property = property;
            this.separator = separator;
            this.preceeding = preceeding;
            this.following = following;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            NodeList nodeList = property.listValueFor(node);
            if (nodeList == null) {
                return;
            }
            if (!nodeList.isEmpty() && preceeding != null) {
                preceeding.prettyPrint(node, printer);
            }
            for (int i=0;i<nodeList.size();i++) {
                genericPrettyPrint(nodeList.get(i), printer);
                if (separator != null && i != (nodeList.size() - 1)) {
                    separator.prettyPrint(node, printer);
                }
            }
            if (!nodeList.isEmpty() && following != null) {
                following.prettyPrint(node, printer);
            }
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

    private static class IfElement implements Element {
        Predicate<Node> predicateCondition;
        private ObservableProperty condition;
        private Element thenElement;
        private Element elseElement;

        public IfElement(Predicate<Node> condition, Element thenElement, Element elseElement) {
            this.predicateCondition = condition;
            this.thenElement = thenElement;
            this.elseElement = elseElement;
        }

        public IfElement(ObservableProperty condition, Element thenElement, Element elseElement) {
            this.condition = condition;
            this.thenElement = thenElement;
            this.elseElement = elseElement;
        }

        public IfElement(ObservableProperty condition, Element thenElement) {
            this.condition = condition;
            this.thenElement = thenElement;
            this.elseElement = null;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            if (condition != null) {
                if (condition.singleValueFor(node) != null) {
                    thenElement.prettyPrint(node, printer);
                } else {
                    if (elseElement != null) {
                        elseElement.prettyPrint(node, printer);
                    }
                }
            } else {
                if (predicateCondition.test(node)) {
                    thenElement.prettyPrint(node, printer);
                } else {
                    if (elseElement != null) {
                        elseElement.prettyPrint(node, printer);
                    }
                }
            }
        }
    }

    private static class SequenceElement implements Element {
        private List<Element> elements;

        public SequenceElement(List<Element> elements) {
            this.elements = elements;
        }

        @Override
        public void prettyPrint(Node node, SourcePrinter printer) {
            elements.forEach(e -> e.prettyPrint(node, printer));
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
            return add(new StringElement(tokenType));
        }

        Builder string(int tokenType, ObservableProperty content) {
            return add(new StringElement(tokenType, content));
        }

        Builder ifThen(ObservableProperty childCondition, Element thenElement) {
            return add(new IfElement(childCondition, thenElement));
        }

        Builder ifThenElse(ObservableProperty childCondition, Element thenElement, Element elseElement) {
            return add(new IfElement(childCondition, thenElement, elseElement));
        }

        Builder ifThenElse(Predicate<Node> predicate, Element thenElement, Element elseElement) {
            return add(new IfElement(predicate, thenElement, elseElement));
        }

        Builder sequence(Element... elements) {
            return add(new SequenceElement(Arrays.asList(elements)));
        }

        Builder list(ObservableProperty listProperty, Element following) {
            return add(new ListElement(listProperty, following));
        }

        Builder list(ObservableProperty listProperty) {
            return add(new ListElement(listProperty));
        }

        Builder list(ObservableProperty property, Element separator, Element preceeding, Element following) {
            return add(new ListElement(property, separator, preceeding, following));
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

    public static String genericPrettyPrint(Node node) {
        SourcePrinter sourcePrinter = new SourcePrinter("    ");
        forClass(node.getClass()).prettyPrint(node, sourcePrinter);
        return sourcePrinter.getSource();
    }

    private static SequenceElement sequence(Element... elements) {
        return new SequenceElement(Arrays.asList(elements));
    }

    private static ChildElement child(ObservableProperty property) {
        return new ChildElement(property);
    }

    private static ListElement list(ObservableProperty property) {
        return new ListElement(property);
    }

    private static ListElement list(ObservableProperty property, Element separator, Element preceeding, Element following) {
        return new ListElement(property, separator, preceeding, following);
    }

    private static StringElement string(int tokenType, String content) {
        return new StringElement(tokenType, content);
    }

    private static StringElement string(int tokenType) {
        return new StringElement(tokenType);
    }

    private static StringElement space() {
        return new StringElement(32, " ");
    }

    private static StringElement comma() {
        return new StringElement(ASTParserConstants.COMMA);
    }

    public static ConcreteSyntaxModel forClass(Class<? extends Node> nodeClazz) {

        if (nodeClazz.equals(ClassExpr.class)) {
            return new Builder().comment().child(TYPE)
                    .string(ASTParserConstants.DOT)
                    .string(ASTParserConstants.CLASS)
                    .build();
        }
        if (nodeClazz.equals(SimpleName.class)) {
            return new Builder().string(ASTParserConstants.IDENTIFIER, ObservableProperty.IDENTIFIER)
                    .build();
        }
        if (nodeClazz.equals(ArrayType.class)) {
            return new Builder()
                    .child(ObservableProperty.COMPONENT_TYPE)
                    .list(ObservableProperty.ANNOTATIONS)
                    .string(ASTParserConstants.LBRACKET)
                    .string(ASTParserConstants.RBRACKET)
                    .build();
        }
        if (nodeClazz.equals(ClassOrInterfaceType.class)) {
            return new Builder().comment()
                    .ifThen(SCOPE, sequence(child(SCOPE), string(ASTParserConstants.DOT)))
                    .list(ANNOTATIONS, space())
                    .child(NAME)
                    .ifThenElse(node -> ((ClassOrInterfaceType)node).isUsingDiamondOperator(),
                            sequence(string(ASTParserConstants.LT), string(ASTParserConstants.GT)),
                            list(TYPE_ARGUMENTS, sequence(comma(), space()), string(ASTParserConstants.LT), string(ASTParserConstants.GT)))
                    .build();
        }

        throw new UnsupportedOperationException("Class " + nodeClazz.getSimpleName());
    }

}
