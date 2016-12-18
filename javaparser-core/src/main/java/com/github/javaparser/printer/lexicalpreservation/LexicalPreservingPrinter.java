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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.*;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.utils.Pair;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;

/**
 * A Lexical Preserving Printer is used to capture all the lexical information while parsing, update them when
 * operating on the AST and then used them to produce code.
 */
public class LexicalPreservingPrinter {

    //
    // Internal types
    //

    /**
     * It knows where to insert elements.
     */
    private interface Inserter {
        void insert(Node parent, Node child);
    }

    private enum InsertionMode {
        PLAIN,
        ON_ITS_OWN_LINE
    }

    //
    // Factory methods
    //

    /**
     * Parse the code and setup the LexicalPreservingPrinter.
     */
    public static <N extends Node> Pair<ParseResult<N>, LexicalPreservingPrinter> setup(ParseStart<N> parseStart, Provider provider) {
        ParseResult<N> parseResult = new JavaParser().parse(parseStart, provider);
        LexicalPreservingPrinter lexicalPreservingPrinter = new LexicalPreservingPrinter(parseResult);
        return new Pair<>(parseResult, lexicalPreservingPrinter);
    }

    //
    // Fields
    //

    /**
     * For each node we setup and update a NodeText, containing all the lexical information about such node
     */
    private Map<Node, NodeText> textForNodes = new IdentityHashMap<>();

    //
    // Constructor and setup
    //

    private LexicalPreservingPrinter(ParseResult<? extends Node> parseResult) {
        // Store initial text
        storeInitialText(parseResult);

        // Setup observer
        AstObserver observer = createObserver(this);
        Node root = parseResult.getResult().get();
        root.registerForSubtree(observer);
    }

    private static AstObserver createObserver(LexicalPreservingPrinter lpp) {
        return new PropagatingAstObserver() {
            @Override
            public void concretePropertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                if (oldValue != null && oldValue.equals(newValue)) {
                    return;
                }
                if (property == ObservableProperty.RANGE) {
                    return;
                }
                throw new UnsupportedOperationException(String.format("Property %s is not supported yet. Old value %s (%s), new value %s (%s)", property, oldValue,
                        oldValue == null ? "": oldValue.getClass(), newValue, newValue == null ? "": newValue.getClass()));
            }

            @Override
            public void concreteListChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                if (type == ListChangeType.REMOVAL) {
                    lpp.updateTextBecauseOfRemovedChild(observedNode, index, observedNode.getParentNode(), nodeAddedOrRemoved);
                } else if (type == ListChangeType.ADDITION) {
                    lpp.updateTextBecauseOfAddedChild(observedNode, index, observedNode.getParentNode(), nodeAddedOrRemoved);
                } else {
                    throw new UnsupportedOperationException();
                }
            }
        };
    }

    private void storeInitialText(ParseResult<? extends Node> parseResult) {
        Node root = parseResult.getResult().get();
        List<JavaToken> documentTokens = parseResult.getTokens().get();
        Map<Node, List<JavaToken>> tokensByNode = new HashMap<>();

        // Take all nodes and sort them to get the leaves first
        List<Node> nodesDepthFirst = new LinkedList<>();
        new TreeVisitor(){
            @Override
            public void process(Node node) {
                nodesDepthFirst.add(node);
            }
        }.visitDepthFirst(root);

        // We go over tokens and find to which nodes belong. Note that we start from the most specific nodes
        // and we move up to more general nodes
        for (JavaToken token : documentTokens) {
            Optional<Node> maybeOwner = nodesDepthFirst.stream().filter(n -> n.getRange().get().contains(token.getRange())).findFirst();
            Node owner = maybeOwner.get();
            if (!tokensByNode.containsKey(owner)) {
                tokensByNode.put(owner, new LinkedList<>());
            }
            tokensByNode.get(owner).add(token);
        }

        // Now that we know the tokens we use them to create the initial NodeText for each node
        new TreeVisitor() {
            @Override
            public void process(Node node) {
                LexicalPreservingPrinter.this.storeInitialTextForOneNode(node, tokensByNode.get(node));
            }
        }.visitBreadthFirst(root);
    }

    private void storeInitialTextForOneNode(Node node, List<JavaToken> nodeTokens) {
        if (nodeTokens == null) {
            nodeTokens = Collections.emptyList();
        }
        List<Pair<Range, TextElement>> elements = new LinkedList<>();
        for (Node child : node.getChildNodes()) {
            elements.add(new Pair<>(child.getRange().get(), new ChildTextElement(this, child)));
        }
        for (JavaToken token : nodeTokens) {
            elements.add(new Pair<>(token.getRange(), new TokenTextElement(token)));
        }
        elements.sort((e1, e2) -> e1.a.begin.compareTo(e2.a.begin));
        textForNodes.put(node, new NodeText(this, elements.stream().map(p -> p.b).collect(Collectors.toList())));
    }

    //
    // Printing methods
    //

    /**
     * Print a Node into a String, preserving the lexical information.
     */
    public String print(Node node) {
        StringWriter writer = new StringWriter();
        try {
            print(node, writer);
        } catch (IOException e) {
            throw new RuntimeException("Unexpected IOException on a StringWriter", e);
        }
        return writer.toString();
    }

    /**
     * Print a Node into a Writer, preserving the lexical information.
     */
    public void print(Node node, Writer writer) throws IOException {
        if (textForNodes.containsKey(node)) {
            final NodeText text = textForNodes.get(node);
            writer.append(text.expand());
        } else {
            writer.append(node.toString());
        }
    }

    //
    // Methods to handle transformations
    //

    private void updateTextBecauseOfRemovedChild(NodeList nodeList, int index, Optional<Node> parentNode, Node child) {
        if (!parentNode.isPresent()) {
            return;
        }
        Node parent = parentNode.get();
        String key = parent.getClass().getSimpleName() + ":" + findNodeListName(nodeList);

        switch (key) {
            case "MethodDeclaration:Parameters":
                if (index == 0 && nodeList.size() > 1) {
                    // we should remove all the text between the child and the comma
                    textForNodes.get(parent).removeTextBetween(child, ASTParserConstants.COMMA, true);
                }
                if (index != 0) {
                    // we should remove all the text between the child and the comma
                    textForNodes.get(parent).removeTextBetween(ASTParserConstants.COMMA, child);
                }
            default:
                textForNodes.get(parent).removeElementForChild(child);
        }
    }

    private void updateTextBecauseOfAddedChild(NodeList nodeList, int index, Optional<Node> parentNode, Node child) {
        if (!parentNode.isPresent()) {
            return;
        }
        Node parent = parentNode.get();
        String nodeListName = findNodeListName(nodeList);

        if (index == 0) {
            // First element of the list, special treatment
            Inserter inserter = getPositionFinder(parent.getClass(), nodeListName);
            inserter.insert(parent, child);
        } else {
            // Element inside the list
            Inserter inserter = insertAfterChild(nodeList.get(index - 1), Separator.COMMA, Separator.SPACE);
            inserter.insert(parent, child);
        }
    }

    private NodeText prettyPrintingTextNode(Node node) {
        // Here we can get the text easily but then we need to figure out how to parse it so that
        // we get the tokens
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    // Visible for testing
    NodeText getOrCreateNodeText(Node node) {
        if (!textForNodes.containsKey(node)) {
            textForNodes.put(node, prettyPrintingTextNode(node));
        }
        return textForNodes.get(node);
    }

    private Inserter insertAfterChild(Method method, Separator... separators) {
        return (parent, child) -> {
            try {
                Node childToFollow = (Node) method.invoke(parent);
                if (childToFollow == null) {
                    throw new IllegalArgumentException();
                }
                insertAfterChild(childToFollow, separators).insert(parent, child);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        };
    }

    private Inserter insertAfterChild(Node childToFollow, Separator... separators) {
        return (parent, child) -> {
                NodeText nodeText = getOrCreateNodeText(parent);
                for (int i=0; i< nodeText.numberOfElements();i++) {
                    TextElement element = nodeText.getTextElement(i);
                    if (element instanceof ChildTextElement) {
                        ChildTextElement childElement = (ChildTextElement)element;
                        if (childElement.getChild() == childToFollow) {
                            for (Separator s : separators) {
                                nodeText.addToken(++i, s);
                            }
                            nodeText.addElement(++i, new ChildTextElement(LexicalPreservingPrinter.this, child));
                            return;
                        }
                    }
                }
                throw new IllegalArgumentException();
        };
    }

    private Inserter insertAfter(final int tokenKind, InsertionMode insertionMode) {
        return (parent, child) -> {
            NodeText nodeText = textForNodes.get(parent);
            for (int i=0; i< nodeText.numberOfElements();i++) {
                TextElement element = nodeText.getTextElement(i);
                if (element instanceof TokenTextElement) {
                    TokenTextElement tokenTextElement = (TokenTextElement)element;
                    if (tokenTextElement.getTokenKind() == tokenKind) {
                        int it = i+1;
                        if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                            nodeText.addToken(it++, Separator.NEWLINE);
                            nodeText.addToken(it++, Separator.TAB);
                        }
                        nodeText.addElement(it++, new ChildTextElement(LexicalPreservingPrinter.this, child));
                        if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                            nodeText.addToken(it++, Separator.NEWLINE);
                        }
                        return;
                    }
                }
            }
            throw new IllegalArgumentException("I could not find the token of type " + tokenKind);
        };
    }

    //
    // Helper methods
    //

    private String findNodeListName(NodeList nodeList) {
        Node parent = nodeList.getParentNodeForChildren();
        for (Method m : parent.getClass().getMethods()) {
            if (m.getParameterCount() == 0 && m.getReturnType().getCanonicalName().equals(NodeList.class.getCanonicalName())) {
                try {
                    NodeList result = (NodeList)m.invoke(parent);
                    if (result == nodeList) {
                        String name = m.getName();
                        if (name.startsWith("get")) {
                            name = name.substring("get".length());
                        }
                        return name;
                    }
                } catch (IllegalAccessException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }
            }
        }
        throw new IllegalArgumentException();
    }

    private Inserter getPositionFinder(Class<?> parentClass, String nodeListName) {
        String key = String.format("%s:%s", parentClass.getSimpleName(), nodeListName);
        switch (key) {
            case "ClassOrInterfaceDeclaration:Members":
                return insertAfter(ASTParserConstants.LBRACE, InsertionMode.ON_ITS_OWN_LINE);
            case "FieldDeclaration:Variables":
                try {
                    return insertAfterChild(FieldDeclaration.class.getMethod("getElementType"), Separator.SPACE);
                } catch (NoSuchMethodException e) {
                    throw new RuntimeException(e);
                }
            case "MethodDeclaration:Parameters":
                return insertAfter(ASTParserConstants.LPAREN, InsertionMode.PLAIN);
            case "BlockStmt:Stmts":
                return insertAfter(ASTParserConstants.LBRACE, InsertionMode.ON_ITS_OWN_LINE);
        }

        throw new UnsupportedOperationException(key);
    }

    // Visible for testing
    NodeText getTextForNode(Node node) {
        return textForNodes.get(node);
    }
}
