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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.Utils;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.GeneratedJavaParserConstants.JAVA_DOC_COMMENT;
import static com.github.javaparser.TokenTypes.eolToken;
import static com.github.javaparser.utils.Utils.decapitalize;

/**
 * A Lexical Preserving Printer is used to capture all the lexical information while parsing, update them when
 * operating on the AST and then used them to produce code.
 */
public class LexicalPreservingPrinter {

    //
    // Factory methods
    //

    /**
     * Parse the code and setup the LexicalPreservingPrinter.
     */
    public static <N extends Node> Pair<ParseResult<N>, LexicalPreservingPrinter> setup(ParseStart<N> parseStart,
                                                                                        Provider provider) {
        ParseResult<N> parseResult = new JavaParser().parse(parseStart, provider);
        if (!parseResult.isSuccessful()) {
            throw new RuntimeException("Parsing failed, unable to setup the lexical preservation printer: "
                    + parseResult.getProblems());
        }
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
                // Not really a change, ignoring
                if ((oldValue != null && oldValue.equals(newValue)) || (oldValue == null && newValue == null)) {
                    return;
                }
                if (property == ObservableProperty.RANGE || property == ObservableProperty.COMMENTED_NODE) {
                    return;
                }
                if (property == ObservableProperty.COMMENT) {
                    if (!observedNode.getParentNode().isPresent()) {
                        throw new IllegalStateException();
                    }
                    NodeText nodeText = lpp.getOrCreateNodeText(observedNode.getParentNode().get());
                    if (oldValue == null && newValue != null) {
                        // Find the position of the comment node and put in front of it the comment and a newline
                        int index = nodeText.findChild(observedNode);
                        nodeText.addChild(index, (Comment)newValue);
                        nodeText.addToken(index + 1, eolToken(), Utils.EOL);
                    } else if (oldValue != null && newValue == null) {
                        if (oldValue instanceof JavadocComment) {
                            JavadocComment javadocComment = (JavadocComment)oldValue;
                            List<TokenTextElement> matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(GeneratedJavaParserConstants.JAVA_DOC_COMMENT)
                            && ((TokenTextElement)e).getText().equals("/**"+javadocComment.getContent()+"*/")).map(e -> (TokenTextElement)e).collect(Collectors.toList());
                            if (matchingTokens.size() != 1) {
                                throw new IllegalStateException();
                            }
                            int index = nodeText.findElement(matchingTokens.get(0));
                            nodeText.removeElement(index);
                            if (nodeText.getElements().get(index).isNewline()) {
                                nodeText.removeElement(index);
                            }
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    } else if (oldValue != null && newValue != null) {
                        if (oldValue instanceof JavadocComment) {
                            JavadocComment oldJavadocComment = (JavadocComment)oldValue;
                            List<TokenTextElement> matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(GeneratedJavaParserConstants.JAVA_DOC_COMMENT)
                                    && ((TokenTextElement)e).getText().equals("/**"+oldJavadocComment.getContent()+"*/")).map(e -> (TokenTextElement)e).collect(Collectors.toList());
                            if (matchingTokens.size() != 1) {
                                throw new IllegalStateException();
                            }
                            JavadocComment newJavadocComment = (JavadocComment)newValue;
                            nodeText.replace(matchingTokens.get(0), new TokenTextElement(JAVA_DOC_COMMENT, "/**" + newJavadocComment.getContent() + "*/"));
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    }
                }
                NodeText nodeText = lpp.getOrCreateNodeText(observedNode);

                if (nodeText == null) {
                    throw new NullPointerException(observedNode.getClass().getSimpleName());
                }

                new LexicalDifferenceCalculator().calculatePropertyChange(nodeText, observedNode, property, oldValue, newValue);
            }

            @Override
            public void concreteListChange(NodeList changedList, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                NodeText nodeText = lpp.getTextForNode(changedList.getParentNodeForChildren());
                if (type == ListChangeType.REMOVAL) {
                    new LexicalDifferenceCalculator().calculateListRemovalDifference(findNodeListName(changedList), changedList, index, nodeAddedOrRemoved).apply(nodeText, changedList.getParentNodeForChildren());
                } else if (type == ListChangeType.ADDITION) {
                    new LexicalDifferenceCalculator().calculateListAdditionDifference(findNodeListName(changedList),changedList, index, nodeAddedOrRemoved).apply(nodeText, changedList.getParentNodeForChildren());
                } else {
                    throw new UnsupportedOperationException();
                }
            }

            @Override
            public void concreteListReplacement(NodeList changedList, int index, Node oldValue, Node newValue) {
                NodeText nodeText = lpp.getTextForNode(changedList.getParentNodeForChildren());
                new LexicalDifferenceCalculator().calculateListReplacementDifference(findNodeListName(changedList), changedList, index, oldValue, newValue).apply(nodeText, changedList.getParentNodeForChildren());
            }
        };
    }

    private void storeInitialText(ParseResult<? extends Node> parseResult) {
        Node root = parseResult.getResult().get();
        List<JavaToken> documentTokens = parseResult.getTokens().get();
        Map<Node, List<JavaToken>> tokensByNode = new IdentityHashMap<>();

        // Take all nodes and sort them to get the leaves first
        List<Node> nodesDepthFirst = new LinkedList<>();
        new TreeVisitor(){
            @Override
            public void process(Node node) {
                // we do not consider "phantom" nodes here, like the fake type of variable in FieldDeclaration
                if (!PhantomNodeLogic.isPhantomNode(node)) {
                    nodesDepthFirst.add(node);
                }
            }
        }.visitLeavesFirst(root);

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
                if (!PhantomNodeLogic.isPhantomNode(node)) {
                    LexicalPreservingPrinter.this.storeInitialTextForOneNode(node, tokensByNode.get(node));
                }
            }
        }.visitBreadthFirst(root);
    }

    private void storeInitialTextForOneNode(Node node, List<JavaToken> nodeTokens) {
        if (nodeTokens == null) {
            nodeTokens = Collections.emptyList();
        }
        List<Pair<Range, TextElement>> elements = new LinkedList<>();
        for (Node child : node.getChildNodes()) {
            if (!PhantomNodeLogic.isPhantomNode(child)) {
                elements.add(new Pair<>(child.getRange().get(), new ChildTextElement(this, child)));
            }
        }
        for (JavaToken token : nodeTokens) {
            elements.add(new Pair<>(token.getRange(), new TokenTextElement(token)));
        }
        elements.sort(Comparator.comparing(e -> e.a.begin));
        textForNodes.put(node, new NodeText(this, elements.stream().map(p -> p.b).collect(Collectors.toList())));
    }

    //
    // Iterators
    //

    public Iterator<TokenTextElement> tokensPreceeding(final Node node) {
        if (!node.getParentNode().isPresent()) {
            return new TextElementIteratorsFactory.EmptyIterator();
        }
        NodeText parentNodeText = getOrCreateNodeText(node.getParentNode().get());
        int index = parentNodeText.findChild(node);
        return new TextElementIteratorsFactory.CascadingIterator<>(
                TextElementIteratorsFactory.partialReverseIterator(parentNodeText, index - 1),
                () -> tokensPreceeding(node.getParentNode().get()));
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

    private NodeText prettyPrintingTextNode(Node node) {
        if (node instanceof PrimitiveType) {
            NodeText nodeText = new NodeText(this);
            PrimitiveType primitiveType = (PrimitiveType)node;
            switch (primitiveType.getType()) {
                case INT:
                    nodeText.addToken(GeneratedJavaParserConstants.INT, node.toString());
                    break;
                default:
                    throw new IllegalArgumentException();
            }
            return nodeText;
        }
        if (node instanceof JavadocComment) {
            NodeText nodeText = new NodeText(this);
            nodeText.addToken(GeneratedJavaParserConstants.JAVA_DOC_COMMENT, "/**"+((JavadocComment)node).getContent()+"*/");
            return nodeText;
        }

        return interpret(node, ConcreteSyntaxModel.forClass(node.getClass()));
    }

    private NodeText interpret(Node node, CsmElement csm) {
        LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(csm, node);
        NodeText nodeText = new NodeText(this);
        for (CsmElement element : calculatedSyntaxModel.elements) {
            if (element instanceof LexicalDifferenceCalculator.CsmChild) {
                nodeText.addChild(((LexicalDifferenceCalculator.CsmChild) element).getChild());
            } else if (element instanceof CsmToken){
                nodeText.addToken(((CsmToken) element).getTokenType(), ((CsmToken) element).getContent(node));
            } else {
                throw new UnsupportedOperationException(element.getClass().getSimpleName());
            }
        }
        return nodeText;
    }

    // Visible for testing
    NodeText getOrCreateNodeText(Node node) {
        if (!textForNodes.containsKey(node)) {
            textForNodes.put(node, prettyPrintingTextNode(node));
        }
        return textForNodes.get(node);
    }

    // Visible for testing
    List<TokenTextElement> findIndentation(Node node) {
        List<TokenTextElement> followingNewlines = new LinkedList<>();
        Iterator<TokenTextElement> it = tokensPreceeding(node);
        while (it.hasNext()) {
            TokenTextElement tte = it.next();
            if (tte.getTokenKind() == GeneratedJavaParserConstants.SINGLE_LINE_COMMENT
                    || tte.isNewline()) {
                break;
            } else {
                followingNewlines.add(tte);
            }
        }
        Collections.reverse(followingNewlines);
        for (int i=0;i<followingNewlines.size();i++){
            if (!followingNewlines.get(i).isSpaceOrTab()) {
                return followingNewlines.subList(0, i);
            }
        }
        return followingNewlines;
    }

    //
    // Helper methods
    //

    private static ObservableProperty findNodeListName(NodeList nodeList) {
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
                        return ObservableProperty.fromCamelCaseName(decapitalize(name));
                    }
                } catch (IllegalAccessException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }
            }
        }
        throw new IllegalArgumentException();
    }

    // Visible for testing
    NodeText getTextForNode(Node node) {
        return textForNodes.get(node);
    }

    @Override
    public String toString() {
        return this.getClass().getSimpleName();
    }
}
