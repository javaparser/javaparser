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
import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.utils.Pair;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.ASTParserConstants.EXTENDS;
import static com.github.javaparser.ASTParserConstants.IMPLEMENTS;
import static com.github.javaparser.printer.lexicalpreservation.NodeText.Option.EXCLUDE_END;
import static com.github.javaparser.printer.lexicalpreservation.NodeText.Option.EXCLUDE_START;
import static com.github.javaparser.printer.lexicalpreservation.NodeText.Option.REMOVE_SPACE_IMMEDIATELY_AFTER;
import static com.github.javaparser.printer.lexicalpreservation.TextElementMatchers.byNode;
import static com.github.javaparser.printer.lexicalpreservation.TextElementMatchers.byTokenType;
import static com.github.javaparser.printer.lexicalpreservation.Tokens.*;
import static com.github.javaparser.utils.Utils.uncapitalize;

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

    /**
     * How should I adapt the whitespace around the element when inserting it?
     */
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
                if (property == ObservableProperty.RANGE) {
                    return;
                }
                NodeText nodeText = lpp.getTextForNode(observedNode);
                // Type requires to be handled in a special way because it is basically a fake node, not part of the
                // AST
                if (property == ObservableProperty.TYPE && observedNode.getParentNode().get() instanceof FieldDeclaration) {
                    // Here we have the infamous phantom nodes so we need to handle this specially
                    // We first of all remove all tokens before the variables. We then print
                    // the common type and a space
                    // behind each variables we put the necessary brackets
                    FieldDeclaration fieldDeclaration = (FieldDeclaration)observedNode.getParentNode().get();
                    FieldDeclaration fieldDeclarationCopy = (FieldDeclaration) fieldDeclaration.clone();
                    int varIndex = fieldDeclaration.getVariables().indexOf(observedNode);
                    fieldDeclarationCopy.getVariable(varIndex).setType((Type) newValue);
                    Type commonType = fieldDeclarationCopy.getCommonType();

                    NodeText fieldNodeText = lpp.getTextForNode(fieldDeclaration);
                    fieldNodeText.removeAllBefore(byNode(fieldDeclaration.getVariable(0)));
                    fieldNodeText.addChild(0, commonType);
                    fieldNodeText.addElement(1, space());
                    return;
                }
                if (oldValue instanceof Comment && newValue instanceof Comment) {
                    NodeText nodeTextForParent = lpp.getOrCreateNodeText(observedNode.getParentNode().get());
                    nodeTextForParent.replaceComment((Comment)oldValue, (Comment)newValue);
                    return;
                }
                if (oldValue instanceof Node && newValue instanceof Node) {
                    nodeText.replace(byNode((Node)oldValue), (Node)newValue);
                    return;
                }
                if (property == ObservableProperty.MODIFIERS) {
                    EnumSet<Modifier> oldModifiers = (EnumSet<Modifier>)oldValue;
                    EnumSet<Modifier> newModifiers = (EnumSet<Modifier>)newValue;
                    oldModifiers.removeAll(newModifiers);
                    newModifiers.removeAll(oldModifiers);
                    oldModifiers.forEach(mToRemove -> nodeText.remove(byTokenType(fromModifier(mToRemove).getTokenKind()), true));
                    newModifiers.forEach(mToAdd -> {
                        nodeText.addElement(0, space());
                        nodeText.addElement(0, fromModifier(mToAdd));
                    });
                    return;
                }
                if (property == ObservableProperty.INITIALIZER) {
                    if (oldValue == null && newValue != null) {
                        nodeText.addElement(space());
                        nodeText.addElement(equal());
                        nodeText.addElement(space());
                        nodeText.addChild((Node)newValue);
                        return;
                    } else if (oldValue != null && newValue == null) {
                        nodeText.removeFromToken(equal(), true);
                        return;
                    }
                }
                if (property == ObservableProperty.DEFAULT_VALUE) {
                    if (oldValue == null && newValue != null) {
                        lpp.insertBefore(byTokenType(ASTParserConstants.SEMICOLON), space(), Tokens.create(ASTParserConstants._DEFAULT), space()).insert(observedNode, (Node)newValue);
                        return;
                    } else if (oldValue != null && newValue == null) {
                        nodeText.removeFromTokenUntil(Tokens.create(ASTParserConstants._DEFAULT), Optional.of(byTokenType(ASTParserConstants.SEMICOLON)), true);
                        return;
                    }
                }
                if (property == ObservableProperty.COMMENT) {
                    if (oldValue == null && newValue != null) {
                        // FIXME consider CompilationUnit which contains its own JavaDoc
                        lpp.insertBefore(byNode(observedNode), true, Tokens.newline()).insert(observedNode.getParentNode().get(), (Node)newValue);
                        return;
                    } else if (oldValue != null && newValue == null) {
                        NodeText nodeTextForParent = lpp.getOrCreateNodeText(observedNode.getParentNode().get());
                        nodeTextForParent.removeComment((Comment)oldValue);
                        return;
                    }
                }
                if (property == ObservableProperty.COMMENTED_NODE) {
                    return;
                }
                if (property == ObservableProperty.IS_INTERFACE) {
                    if ((Boolean)newValue) {
                        nodeText.replace(byTokenType(ASTParserConstants.CLASS), new TokenTextElement(ASTParserConstants.INTERFACE, "interface"));
                    } else {
                        nodeText.replace(byTokenType(ASTParserConstants.INTERFACE), new TokenTextElement(ASTParserConstants.CLASS, "class"));
                    }
                    return;
                }
                if (property == ObservableProperty.IS_STATIC) {
                    if ((Boolean)newValue) {
                        nodeText.addElement(0, new TokenTextElement(ASTParserConstants.STATIC, "static"));
                        nodeText.addElement(1, new TokenTextElement(0, " "));
                    } else {
                        nodeText.remove(byTokenType(ASTParserConstants.STATIC), true);
                    }
                    return;
                }
                if (property == ObservableProperty.DIMENSION) {
                    if (newValue == null) {
                        nodeText.remove(byNode((Node)oldValue));
                    } else {
                        lpp.insertAfter(byTokenType(ASTParserConstants.LBRACKET), InsertionMode.PLAIN).insert(observedNode, (Node)newValue);
                    }
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
        elements.sort((e1, e2) -> e1.a.begin.compareTo(e2.a.begin));
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

    private void updateTextBecauseOfRemovedChild(NodeList nodeList, int index, Optional<Node> parentNode, Node child) {
        if (!parentNode.isPresent()) {
            return;
        }
        Node parent = parentNode.get();
        QualifiedProperty property = new QualifiedProperty(parent.getClass(), findNodeListName(nodeList));

        if (property.getObservableProperty() == ObservableProperty.PARAMETERS) {
            if (index == 0 && nodeList.size() > 1) {
                // we should remove all the text between the child and the comma
                textForNodes.get(parent).removeTextBetween(byNode(child), byTokenType(ASTParserConstants.COMMA), EnumSet.of(REMOVE_SPACE_IMMEDIATELY_AFTER));
            }
            if (index != 0) {
                // we should remove all the text between the child and the comma
                textForNodes.get(parent).removeTextBetween(byTokenType(ASTParserConstants.COMMA), byNode(child));
            }
        }

        if (property.getObservableProperty() == ObservableProperty.EXTENDED_TYPES) {
            if (index == 0 && nodeList.size() == 1) {
                textForNodes.get(parent).removeTextBetween(byTokenType(EXTENDS), byNode(child), EnumSet.of(REMOVE_SPACE_IMMEDIATELY_AFTER));
            }
        }

        if (property.getObservableProperty() == ObservableProperty.IMPLEMENTED_TYPES) {
            if (index == 0 && nodeList.size() == 1) {
                textForNodes.get(parent).removeTextBetween(byTokenType(ASTParserConstants.IMPLEMENTS), byNode(child), EnumSet.of(REMOVE_SPACE_IMMEDIATELY_AFTER));
            }
        }

        if (property.getObservableProperty() == ObservableProperty.ANNOTATIONS) {
            textForNodes.get(parent).removeWhiteSpaceFollowing(byNode(child));
        }

        if (property.isInOwnLine()) {
            for (Iterator<TokenTextElement> it = tokensPreceeding(child); it.hasNext();) {
               // Removing preceeding whitespace tokens until we reach a newline
               TokenTextElement tte = it.next();
               if (tte.getTokenKind() != 1 && tte.getTokenKind() !=3) {
                   break;
               }
               it.remove();
               if (tte.getTokenKind() == 3) {
                   break;
               }
            }
        }

        textForNodes.get(parent).remove(byNode(child));
    }

    private void updateTextBecauseOfAddedChild(NodeList nodeList, int index, Optional<Node> parentNode, Node child) {
        if (!parentNode.isPresent()) {
            return;
        }
        Node parent = parentNode.get();
        QualifiedProperty property = new QualifiedProperty(parent.getClass(), findNodeListName(nodeList));

        if (index == 0) {
            // First element of the list, special treatment
            Inserter inserter = getPositionFinder(property, parent, nodeList, index);
            inserter.insert(parent, child);
        } else {
            // Element inside the list
            Inserter inserter = insertAfterChild(nodeList.get(index - 1), property.isInOwnLine(), property.separators());
            inserter.insert(parent, child);
        }
    }

    private NodeText prettyPrintingTextNode(Node node) {
        if (node instanceof PrimitiveType) {
            NodeText nodeText = new NodeText(this);
            PrimitiveType primitiveType = (PrimitiveType)node;
            switch (primitiveType.getType()) {
                case INT:
                    nodeText.addToken(ASTParserConstants.INT, node.toString());
                    break;
                default:
                    throw new IllegalArgumentException();
            }
            return nodeText;
        }

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

    private Inserter insertAfterChild(ObservableProperty property, TokenTextElement... separators) {
        return (parent, child) -> {
            Node childToFollow = property.singleValueFor(parent);
            if (childToFollow == null) {
                throw new IllegalArgumentException();
            }
            insertAfterChild(childToFollow, false, separators).insert(parent, child);
        };
    }

    private Inserter insertBefore(TextElementMatcher delimiter, boolean onIsOwnLine, TokenTextElement... separators) {
        return (parent, child) -> {
            NodeText nodeText = getOrCreateNodeText(parent);
            for (int i=0; i< nodeText.numberOfElements();i++) {
                TextElement element = nodeText.getTextElement(i);
                if (delimiter.match(element)) {
                    if (onIsOwnLine) {
                        //nodeText.addToken(i--, Separator.NEWLINE);
                        /*for (TokenTextElement e : findIndentation(childToPreceed)) {
                            nodeText.addElement(++i, e);
                        }*/
                    }
                    /*for (Separator s : separators) {
                        nodeText.addToken(++i, s);
                    }*/
                    nodeText.addElement(i--, new ChildTextElement(LexicalPreservingPrinter.this, child));
                    return;
                }
            }
            throw new IllegalArgumentException();
        };
    }

    private Inserter insertAfterChild(Node childToFollow, boolean onIsOwnLine, TextElement... separators) {
        return insertAfterChild(childToFollow, onIsOwnLine, separators, new TokenTextElement[]{});
    }

    private Inserter insertAfterChild(Node childToFollow, boolean onIsOwnLine, TextElement[] before, TextElement[] after) {
        return (parent, child) -> {
            NodeText nodeText = getOrCreateNodeText(parent);
            for (int i=0; i< nodeText.numberOfElements();i++) {
                TextElement element = nodeText.getTextElement(i);
                if (element instanceof ChildTextElement) {
                    ChildTextElement childElement = (ChildTextElement)element;
                    if (childElement.getChild() == childToFollow) {
                        if (onIsOwnLine) {
                            nodeText.addElement(++i, Tokens.newline());
                            for (TokenTextElement e : findIndentation(childToFollow)) {
                                nodeText.addElement(++i, e);
                            }
                        }
                        for (TextElement e : before) {
                            nodeText.addElement(++i, e);
                        }
                        nodeText.addElement(++i, new ChildTextElement(LexicalPreservingPrinter.this, child));
                        for (TextElement e : after) {
                            nodeText.addElement(++i, e);
                        }
                        return;
                    }
                }
            }
            throw new IllegalArgumentException();
        };
    }

    private Node skipToMeaningful(Node node) {
        if (node instanceof BlockStmt) {
            return skipToMeaningful(node.getParentNode().get());
        }
        return node;
    }

    private Inserter insertBefore(final TextElementMatcher delimiter, TextElement... separators) {
        return (parent, child) -> {
            NodeText nodeText = textForNodes.get(parent);
            for (int i=0; i< nodeText.numberOfElements();i++) {
                TextElement element = nodeText.getTextElement(i);
                if (delimiter.match(element)) {
                    int pos = i;
                    for (TextElement s : separators) {
                        nodeText.addElement(pos++, s);
                    }
                    nodeText.addElement(pos++, new ChildTextElement(LexicalPreservingPrinter.this, child));
                    return;
                }
            }
            throw new IllegalArgumentException("I could not find the token of type " + delimiter);
        };
    }

    private Inserter insertAfter(TextElementMatcher delimiter, InsertionMode insertionMode, TextElement[] separatorsBefore, TextElement[] separatorsAfter) {
        return (parent, child) -> {
            NodeText nodeText = textForNodes.get(parent);
            for (int i=0; i< nodeText.numberOfElements();i++) {
                TextElement element = nodeText.getTextElement(i);
                List<TokenTextElement> parentIndentation = findIndentation(skipToMeaningful(parent));
                if (delimiter.match(element)) {
                    int it = i+1;
                    if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                        nodeText.addElement(it++, Tokens.newline());
                        for (TokenTextElement e : parentIndentation) {
                            nodeText.addElement(it++, e);
                        }
                        nodeText.addElement(it++, tab());
                    }
                    for (TextElement s : separatorsBefore) {
                        nodeText.addElement(it++, s);
                    }
                    nodeText.addElement(it++, new ChildTextElement(LexicalPreservingPrinter.this, child));
                    for (TextElement s : separatorsAfter) {
                        nodeText.addElement(it++, s);
                    }
                    if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                        nodeText.addElement(it++, Tokens.newline());
                        for (TokenTextElement e : parentIndentation) {
                            nodeText.addElement(it++, e);
                        }
                    }
                    return;
                }
            }
            throw new IllegalArgumentException("I could not find the child " + delimiter);
        };
    }

    private Inserter insertAfter(TextElementMatcher delimiter, InsertionMode insertionMode, TextElement[] separators) {
        return (parent, child) -> {
            NodeText nodeText = textForNodes.get(parent);
            for (int i=0; i< nodeText.numberOfElements();i++) {
                TextElement element = nodeText.getTextElement(i);
                List<TokenTextElement> parentIndentation = findIndentation(skipToMeaningful(parent));
                if (delimiter.match(element)) {
                    int it = i+1;
                    if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                        nodeText.addElement(it++, newline());
                        for (TokenTextElement e : parentIndentation) {
                            nodeText.addElement(it++, e);
                        }
                        nodeText.addElement(it++, tab());
                    }
                    nodeText.addElement(it++, new ChildTextElement(LexicalPreservingPrinter.this, child));
                    for (TextElement s : separators) {
                        nodeText.addElement(it++, s);
                    }
                    if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                        nodeText.addElement(it++, newline());
                        for (TokenTextElement e : parentIndentation) {
                            nodeText.addElement(it++, e);
                        }
                    }
                    return;
                }
            }
            throw new IllegalArgumentException("I could not find the token of type " + delimiter + ". NodeText: " + nodeText);
        };
    }

    private Inserter insertAfter(TextElementMatcher delimiter, InsertionMode insertionMode) {
       return insertAfter(delimiter, insertionMode, new TokenTextElement[]{});
    }

    // Visible for testing
    List<TokenTextElement> findIndentation(Node node) {
        List<TokenTextElement> elements = new LinkedList<>();
        Iterator<TokenTextElement> it = tokensPreceeding(node);
        while (it.hasNext()) {
            TokenTextElement tte = it.next();
            // For some reason 3 is used as token kind of newlines
            if (tte.getTokenKind() != 1) {
                return elements;
            }
            if (tte.getTokenKind() == ASTParserConstants.SINGLE_LINE_COMMENT
                    || tte.getTokenKind() == Tokens.newline().getTokenKind()) {
                return elements;
            }
            elements.add(tte);
        }
        return elements;
    }

    //
    // Helper methods
    //

    private ObservableProperty findNodeListName(NodeList nodeList) {
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
                        return ObservableProperty.fromCamelCaseName(uncapitalize(name));
                    }
                } catch (IllegalAccessException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }
            }
        }
        throw new IllegalArgumentException();
    }

    private Inserter getPositionFinder(QualifiedProperty property, Node parent, NodeList nodeList, int index) {
        if (property.equals(new QualifiedProperty(ClassOrInterfaceDeclaration.class, ObservableProperty.MEMBERS))) {
            if (nodeList.isEmpty()) {
                getOrCreateNodeText(parent).removeTextBetween(byTokenType(ASTParserConstants.LBRACE), byTokenType(ASTParserConstants.RBRACE),
                        EnumSet.of(EXCLUDE_START, EXCLUDE_END));
            }
            return insertAfter(byTokenType(ASTParserConstants.LBRACE), InsertionMode.ON_ITS_OWN_LINE);
        } else if (property.equals(new QualifiedProperty(FieldDeclaration.class, ObservableProperty.VARIABLES))) {
            return insertAfterChild(ObservableProperty.ELEMENT_TYPE, space());
        } else if (property.getObservableProperty() == ObservableProperty.PARAMETERS) {
            return insertAfter(byTokenType(ASTParserConstants.LPAREN), InsertionMode.PLAIN);
        }  else if (property.equals(new QualifiedProperty(BlockStmt.class, ObservableProperty.STATEMENTS))) {
            if (nodeList.isEmpty()) {
                getOrCreateNodeText(parent).removeTextBetween(byTokenType(ASTParserConstants.LBRACE), byTokenType(ASTParserConstants.RBRACE),
                        EnumSet.of(EXCLUDE_START, EXCLUDE_END));
            }
            return insertAfter(byTokenType(ASTParserConstants.LBRACE), InsertionMode.ON_ITS_OWN_LINE);
        }  else if (property.equals(new QualifiedProperty(ClassOrInterfaceDeclaration.class, ObservableProperty.TYPE_PARAMETERS))) {
            if (nodeList.isEmpty()) {
                return insertAfterChild(((ClassOrInterfaceDeclaration) parent).getName(), false,
                        new TokenTextElement[]{new TokenTextElement(ASTParserConstants.LT, "<")},
                        new TokenTextElement[]{new TokenTextElement(ASTParserConstants.GT, ">")});
            } else {
                if (nodeList.size() == index) {
                    return insertAfter(byTokenType(ASTParserConstants.LT), InsertionMode.PLAIN);
                } else {
                    return insertAfter(byTokenType(ASTParserConstants.LT), InsertionMode.PLAIN, property.separators());
                }
            }
        } else if (property.getObservableProperty() == ObservableProperty.ANNOTATIONS) {
            if (property.getContainerClass().equals(ArrayCreationLevel.class)) {
                return insertAtBeginning(InsertionMode.PLAIN);
            }
            return insertAtBeginning(InsertionMode.ON_ITS_OWN_LINE);
        } else if (property.getObservableProperty() == ObservableProperty.EXTENDED_TYPES) {
            SimpleName name = ((ClassOrInterfaceDeclaration)parent).getName();
            return insertAfter(byNode(name), InsertionMode.PLAIN, new TextElement[]{space(), Tokens.create(EXTENDS), space()}, new TextElement[]{});
        } else if (property.getObservableProperty() == ObservableProperty.IMPLEMENTED_TYPES) {
            SimpleName name = ((ClassOrInterfaceDeclaration)parent).getName();
            return insertAfter(byNode(name), InsertionMode.PLAIN, new TextElement[]{space(), Tokens.create(IMPLEMENTS), space()}, new TextElement[]{});
        } else {
            throw new UnsupportedOperationException("I do not know how to find the position of " + property);
        }
    }

    private Inserter insertAtBeginning(InsertionMode insertionMode) {
        return (parent, child) -> {
            getOrCreateNodeText(parent).addElement(0, new ChildTextElement(this, child));
            if (insertionMode == InsertionMode.ON_ITS_OWN_LINE) {
                getOrCreateNodeText(parent).addElement(1, new TokenTextElement(3, "\n"));
            }
        };
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
