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
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.Utils;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.decapitalize;
import static java.util.Comparator.*;

/**
 * A Lexical Preserving Printer is used to capture all the lexical information while parsing, update them when
 * operating on the AST and then used them to reproduce the source code
 * in its original formatting including the AST changes.
 */
public class LexicalPreservingPrinter {

    /**
     * The nodetext for a node is stored in the node's data field. This is the key to set and retrieve it.
     */
    public static final DataKey<NodeText> NODE_TEXT_DATA = new DataKey<NodeText>() {
    };

    //
    // Factory methods
    //

    /**
     * Parse the code and setup the LexicalPreservingPrinter.
     *
     * @deprecated use setup(Node) and the static methods on this class.
     */
    public static <N extends Node> Pair<ParseResult<N>, LexicalPreservingPrinter> setup(ParseStart<N> parseStart,
                                                                                        Provider provider) {
        ParseResult<N> parseResult = new JavaParser().parse(parseStart, provider);
        if (!parseResult.isSuccessful()) {
            throw new RuntimeException("Parsing failed, unable to setup the lexical preservation printer: "
                    + parseResult.getProblems());
        }
        LexicalPreservingPrinter lexicalPreservingPrinter = new LexicalPreservingPrinter(parseResult.getResult().get());
        return new Pair<>(parseResult, lexicalPreservingPrinter);
    }

    /**
     * Prepares the node so it can be used in the print methods.
     * The correct order is:
     * <ol>
     * <li>Parse some code</li>
     * <li>Call this setup method on the result</li>
     * <li>Make changes to the AST as desired</li>
     * <li>Use one of the print methods on this class to print out the original source code with your changes added</li>
     * </ol>
     *
     * @return the node passed as a parameter for your convenience.
     */
    public static <N extends Node> N setup(N node) {
        assertNotNull(node);

        node.getTokenRange().ifPresent(r -> {
            storeInitialText(node);

            // Setup observer
            AstObserver observer = createObserver();

            node.registerForSubtree(observer);
        });
        return node;
    }

    //
    // Constructor and setup
    //

    /**
     * @deprecated use setup(Node) to prepare a node for lexical preservation,
     * then use the static methods on this class to print it.
     */
    @Deprecated
    public LexicalPreservingPrinter(Node node) {
        setup(node);
    }

    private static AstObserver createObserver() {
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
                    NodeText nodeText = getOrCreateNodeText(observedNode.getParentNode().get());
                    if (oldValue == null) {
                        // Find the position of the comment node and put in front of it the comment and a newline
                        int index = nodeText.findChild(observedNode);
                        nodeText.addChild(index, (Comment) newValue);
                        nodeText.addToken(index + 1, eolTokenKind(), Utils.EOL);
                    } else if (newValue == null) {
                        if (oldValue instanceof JavadocComment) {
                            JavadocComment javadocComment = (JavadocComment) oldValue;
                            List<TokenTextElement> matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(JAVADOC_COMMENT)
                                    && ((TokenTextElement) e).getText().equals("/**" + javadocComment.getContent() + "*/")).map(e -> (TokenTextElement) e).collect(Collectors.toList());
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
                    } else {
                        if (oldValue instanceof JavadocComment) {
                            JavadocComment oldJavadocComment = (JavadocComment) oldValue;
                            List<TokenTextElement> matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(JAVADOC_COMMENT)
                                    && ((TokenTextElement) e).getText().equals("/**" + oldJavadocComment.getContent() + "*/")).map(e -> (TokenTextElement) e).collect(Collectors.toList());
                            if (matchingTokens.size() != 1) {
                                throw new IllegalStateException();
                            }
                            JavadocComment newJavadocComment = (JavadocComment) newValue;
                            nodeText.replace(matchingTokens.get(0), new TokenTextElement(JAVADOC_COMMENT, "/**" + newJavadocComment.getContent() + "*/"));
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    }
                }
                NodeText nodeText = getOrCreateNodeText(observedNode);

                if (nodeText == null) {
                    throw new NullPointerException(observedNode.getClass().getSimpleName());
                }

                new LexicalDifferenceCalculator().calculatePropertyChange(nodeText, observedNode, property, oldValue, newValue);
            }

            @Override
            public void concreteListChange(NodeList changedList, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                NodeText nodeText = getOrCreateNodeText(changedList.getParentNodeForChildren());
                if (type == ListChangeType.REMOVAL) {
                    new LexicalDifferenceCalculator().calculateListRemovalDifference(findNodeListName(changedList), changedList, index).apply(nodeText, changedList.getParentNodeForChildren());
                } else if (type == ListChangeType.ADDITION) {
                    new LexicalDifferenceCalculator().calculateListAdditionDifference(findNodeListName(changedList), changedList, index, nodeAddedOrRemoved).apply(nodeText, changedList.getParentNodeForChildren());
                } else {
                    throw new UnsupportedOperationException();
                }
            }

            @Override
            public void concreteListReplacement(NodeList changedList, int index, Node oldValue, Node newValue) {
                NodeText nodeText = getOrCreateNodeText(changedList.getParentNodeForChildren());
                new LexicalDifferenceCalculator().calculateListReplacementDifference(findNodeListName(changedList), changedList, index, newValue).apply(nodeText, changedList.getParentNodeForChildren());
            }
        };
    }

    private static void storeInitialText(Node root) {
        Map<Node, List<JavaToken>> tokensByNode = new IdentityHashMap<>();

        // We go over tokens and find to which nodes they belong. Note that we do not traverse the tokens as they were
        // on a list but as they were organized in a tree. At each time we select only the branch corresponding to the
        // range of interest and ignore all other branches
        for (JavaToken token : root.getTokenRange().get()) {
            Range tokenRange = token.getRange().orElseThrow(() -> new RuntimeException("Token without range: " + token));
            Node owner = findNodeForToken(root, tokenRange);
            if (owner == null) {
                throw new RuntimeException("Token without node owning it: " + token);
            }
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
                    LexicalPreservingPrinter.storeInitialTextForOneNode(node, tokensByNode.get(node));
                }
            }
        }.visitBreadthFirst(root);
    }

    private static Node findNodeForToken(Node node, Range tokenRange) {
        if (PhantomNodeLogic.isPhantomNode(node)) {
            return null;
        }
        if (node.getRange().get().contains(tokenRange)) {
            for (Node child : node.getChildNodes()) {
                Node found = findNodeForToken(child, tokenRange);
                if (found != null) {
                    return found;
                }
            }
            return node;
        } else {
            return null;
        }
    }

    private static void storeInitialTextForOneNode(Node node, List<JavaToken> nodeTokens) {
        if (nodeTokens == null) {
            nodeTokens = Collections.emptyList();
        }
        List<Pair<Range, TextElement>> elements = new LinkedList<>();
        for (Node child : node.getChildNodes()) {
            if (!PhantomNodeLogic.isPhantomNode(child)) {
                if (!child.getRange().isPresent()) {
                    throw new RuntimeException("Range not present on node " + child);
                }
                elements.add(new Pair<>(child.getRange().get(), new ChildTextElement(child)));
            }
        }
        for (JavaToken token : nodeTokens) {
            elements.add(new Pair<>(token.getRange().get(), new TokenTextElement(token)));
        }
        elements.sort(comparing(e -> e.a.begin));
        node.setData(NODE_TEXT_DATA, new NodeText(elements.stream().map(p -> p.b).collect(Collectors.toList())));
    }

    //
    // Iterators
    //

    private static Iterator<TokenTextElement> tokensPreceeding(final Node node) {
        if (!node.getParentNode().isPresent()) {
            return new TextElementIteratorsFactory.EmptyIterator<>();
        }
        // There is the awfully painful case of the fake types involved in variable declarators and
        // fields or variable declaration that are, of course, an exception...

        NodeText parentNodeText = getOrCreateNodeText(node.getParentNode().get());
        int index = parentNodeText.tryToFindChild(node);
        if (index == NodeText.NOT_FOUND) {
            if (node.getParentNode().get() instanceof VariableDeclarator) {
                return tokensPreceeding(node.getParentNode().get());
            } else {
                throw new IllegalArgumentException(
                        String.format("I could not find child '%s' in parent '%s'. parentNodeText: %s",
                                node, node.getParentNode().get(), parentNodeText));
            }
        }

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
    public static String print(Node node) {
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
    public static void print(Node node, Writer writer) throws IOException {
        if (!node.containsData(NODE_TEXT_DATA)) {
            getOrCreateNodeText(node);
        }
        final NodeText text = node.getData(NODE_TEXT_DATA);
        writer.append(text.expand());
    }

    //
    // Methods to handle transformations
    //

    private static void prettyPrintingTextNode(Node node, NodeText nodeText) {
        if (node instanceof PrimitiveType) {
            PrimitiveType primitiveType = (PrimitiveType) node;
            switch (primitiveType.getType()) {
                case BOOLEAN:
                    nodeText.addToken(BOOLEAN, node.toString());
                    break;
                case CHAR:
                    nodeText.addToken(CHAR, node.toString());
                    break;
                case BYTE:
                    nodeText.addToken(BYTE, node.toString());
                    break;
                case SHORT:
                    nodeText.addToken(SHORT, node.toString());
                    break;
                case INT:
                    nodeText.addToken(INT, node.toString());
                    break;
                case LONG:
                    nodeText.addToken(LONG, node.toString());
                    break;
                case FLOAT:
                    nodeText.addToken(FLOAT, node.toString());
                    break;
                case DOUBLE:
                    nodeText.addToken(DOUBLE, node.toString());
                    break;
                default:
                    throw new IllegalArgumentException();
            }
            return;
        }
        if (node instanceof JavadocComment) {
            nodeText.addToken(JAVADOC_COMMENT, "/**" + ((JavadocComment) node).getContent() + "*/");
            return;
        }

        interpret(node, ConcreteSyntaxModel.forClass(node.getClass()), nodeText);
    }

    private static NodeText interpret(Node node, CsmElement csm, NodeText nodeText) {
        LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(csm, node);

        List<TokenTextElement> indentation = findIndentation(node);

        boolean pendingIndentation = false;
        for (CsmElement element : calculatedSyntaxModel.elements) {
            if (pendingIndentation && !(element instanceof CsmToken && ((CsmToken) element).isNewLine())) {
                indentation.forEach(nodeText::addElement);
            }
            pendingIndentation = false;
            if (element instanceof LexicalDifferenceCalculator.CsmChild) {
                nodeText.addChild(((LexicalDifferenceCalculator.CsmChild) element).getChild());
            } else if (element instanceof CsmToken) {
                CsmToken csmToken = (CsmToken) element;
                nodeText.addToken(csmToken.getTokenType(), csmToken.getContent(node));
                if (csmToken.isNewLine()) {
                    pendingIndentation = true;
                }
            } else if (element instanceof CsmMix) {
                CsmMix csmMix = (CsmMix) element;
                csmMix.getElements().forEach(e -> interpret(node, e, nodeText));
            } else {
                throw new UnsupportedOperationException(element.getClass().getSimpleName());
            }
        }
        // Array brackets are a pain... we do not have a way to represent them explicitly in the AST
        // so they have to be handled in a special way
        if (node instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator) node;
            variableDeclarator.getParentNode().ifPresent(parent ->
                    ((NodeWithVariables<?>) parent).getMaximumCommonType().ifPresent(mct -> {
                        int extraArrayLevels = variableDeclarator.getType().getArrayLevel() - mct.getArrayLevel();
                        for (int i = 0; i < extraArrayLevels; i++) {
                            nodeText.addElement(new TokenTextElement(LBRACKET));
                            nodeText.addElement(new TokenTextElement(RBRACKET));
                        }
                    })
            );
        }
        return nodeText;
    }

    // Visible for testing
    static NodeText getOrCreateNodeText(Node node) {
        if (!node.containsData(NODE_TEXT_DATA)) {
            NodeText nodeText = new NodeText();
            node.setData(NODE_TEXT_DATA, nodeText);
            prettyPrintingTextNode(node, nodeText);
        }
        return node.getData(NODE_TEXT_DATA);
    }

    // Visible for testing
    static List<TokenTextElement> findIndentation(Node node) {
        List<TokenTextElement> followingNewlines = new LinkedList<>();
        Iterator<TokenTextElement> it = tokensPreceeding(node);
        while (it.hasNext()) {
            TokenTextElement tte = it.next();
            if (tte.getTokenKind() == SINGLE_LINE_COMMENT
                    || tte.isNewline()) {
                break;
            } else {
                followingNewlines.add(tte);
            }
        }
        Collections.reverse(followingNewlines);
        for (int i = 0; i < followingNewlines.size(); i++) {
            if (!followingNewlines.get(i).isSpaceOrTab()) {
                return followingNewlines.subList(0, i);
            }
        }
        return followingNewlines;
    }

    //
    // Helper methods
    //

    private static boolean isReturningOptionalNodeList(Method m) {
        if (!m.getReturnType().getCanonicalName().equals(Optional.class.getCanonicalName())) {
            return false;
        }
        if (!(m.getGenericReturnType() instanceof ParameterizedType)) {
            return false;
        }
        ParameterizedType parameterizedType = (ParameterizedType) m.getGenericReturnType();
        java.lang.reflect.Type optionalArgument = parameterizedType.getActualTypeArguments()[0];
        return (optionalArgument.getTypeName().startsWith(NodeList.class.getCanonicalName()));
    }

    private static ObservableProperty findNodeListName(NodeList nodeList) {
        Node parent = nodeList.getParentNodeForChildren();
        for (Method m : parent.getClass().getMethods()) {
            if (m.getParameterCount() == 0 && m.getReturnType().getCanonicalName().equals(NodeList.class.getCanonicalName())) {
                try {
                    Object raw = m.invoke(parent);
                    if (!(raw instanceof NodeList)) {
                        throw new IllegalStateException("Expected NodeList, found " + raw.getClass().getCanonicalName());
                    }
                    NodeList result = (NodeList) raw;
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
            } else if (m.getParameterCount() == 0 && isReturningOptionalNodeList(m)) {
                try {
                    Optional<NodeList<?>> raw = (Optional<NodeList<?>>) m.invoke(parent);
                    if (raw.isPresent() && raw.get() == nodeList) {
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
        throw new IllegalArgumentException("Cannot find list name of NodeList of size " + nodeList.size());
    }
}
