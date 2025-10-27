/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.decapitalize;
import static java.util.Comparator.comparing;
import static java.util.stream.Collectors.toList;

import com.github.javaparser.JavaToken;
import com.github.javaparser.Range;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.*;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import com.github.javaparser.utils.LineSeparator;
import com.github.javaparser.utils.Pair;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.util.*;

/**
 * The LexicalPreservingPrinter is responsible for maintaining the original formatting
 * and layout of Java source code when the Abstract Syntax Tree (AST) is modified.
 *
 * This printer works by:
 * 1. Storing the original textual representation alongside the AST nodes
 * 2. Tracking changes made to the AST through a sophisticated change tracking system
 * 3. Applying only the necessary modifications while preserving unchanged portions
 * 4. Maintaining original spacing, comments, and formatting wherever possible
 *
 * The lexical preservation is essential for code refactoring tools that need to
 * modify code while maintaining its original style and readability.
 *
 * Usage Pattern:
 * 1. Setup lexical preservation on a CompilationUnit before making changes
 * 2. Modify the AST as needed
 * 3. Use this printer to generate the modified source code with preserved formatting
 */
public class LexicalPreservingPrinter {

    private static String JAVA_UTIL_OPTIONAL = Optional.class.getCanonicalName();

    private static String JAVAPARSER_AST_NODELIST = NodeList.class.getCanonicalName();

    /**
     * Observer tracks changes made to AST nodes.
     * The observer is responsible for detecting modifications to specific types
     * of nodes and updating the lexical preservation data accordingly.
     */
    private static AstObserver observer;

    /**
     * The nodetext for a node is stored in the node's data field. This is the key to set and retrieve it.
     */
    public static final DataKey<NodeText> NODE_TEXT_DATA = new DataKey<NodeText>() {};

    private static final LexicalDifferenceCalculator LEXICAL_DIFFERENCE_CALCULATOR = new LexicalDifferenceCalculator();

    //
    // Factory methods
    //
    /**
     * Initializes lexical preservation for the given CompilationUnit.
     * This method must be called before making any modifications to the AST
     * if you want to preserve the original formatting.
     *
     * The setup process involves:
     * 1. Parsing the original source code into tokens
     * 2. Creating NodeText representations for each AST node
     * 3. Establishing relationships between tokens and nodes
     * 4. Setting up change observers to track future modifications
     *
     * @param cu The CompilationUnit to setup for lexical preservation
     * @return The same CompilationUnit with lexical preservation enabled
     */
    public static <N extends Node> N setup(N node) {
        assertNotNull(node);
        if (observer == null) {
            observer = createObserver();
        }
        node.getTokenRange().ifPresent(r -> {
            storeInitialText(node);
            // Setup observer
            if (!node.isRegistered(observer)) {
                node.registerForSubtree(observer);
            }
        });
        return node;
    }

    /*
     * Returns true if the lexical preserving printer is initialized on the node
     */
    public static boolean isAvailableOn(Node node) {
        return node.containsData(NODE_TEXT_DATA);
    }

    //
    // Constructor and setup
    //
    private static AstObserver createObserver() {
        return new LexicalPreservingPrinter.Observer();
    }

    private static class Observer extends PropagatingAstObserver {

        @Override
        public void concretePropertyChange(
                Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
            if (oldValue == newValue) {
                // Not really a change, ignore
                return;
            }
            if (property == ObservableProperty.RANGE || property == ObservableProperty.COMMENTED_NODE) {
                return;
            }
            if (property == ObservableProperty.COMMENT) {
                Optional<Node> parentNode = observedNode.getParentNode();
                NodeText nodeText = parentNode
                        .map(parent -> getOrCreateNodeText(parentNode.get()))
                        .orElseGet(() -> getOrCreateNodeText(observedNode));
                if (oldValue == null) {
                    // this case corresponds to the addition of a comment
                    // Find the position of the comment node and put in front of it the [...]
                    int index = parentNode.isPresent() ? nodeText.findChild(observedNode) : 0;
                    /* Add the same indentation to the comment as the previous node
                     * for example if we want to add a comment on the body of the method declaration :
                     * Actual code
                     * {@code
                     * public class Foo {
                     *   void visit(final UnknownType n, final Void arg)
                     *   {
                     *   }
                     * }
                     * }
                     * Expected result
                     * {@code
                     * public class Foo {
                     *   void visit(final UnknownType n, final Void arg)
                     *   //added comment <-- we should insert indentation before the comment
                     *   {
                     *   }
                     * }
                     * }
                     */
                    fixIndentOfAddedNode(nodeText, index - 1);
                    LineSeparator lineSeparator = observedNode.getLineEndingStyleOrDefault(LineSeparator.SYSTEM);
                    for (TokenTextElement element : makeCommentTokens((Comment) newValue)) {
                        nodeText.addElement(index++, element);
                    }
                    nodeText.addToken(index, eolTokenKind(lineSeparator), lineSeparator.asRawString());
                    // code indentation after inserting an eol token may be wrong
                } else if (newValue == null) {
                    // this case corresponds to a deletion of a comment
                    if (oldValue instanceof Comment) {
                        if (((Comment) oldValue).isOrphan()) {
                            nodeText = getOrCreateNodeText(observedNode);
                        }
                        Pair<Integer, Integer> indexAndCount =
                                getIndexAndCountOfCommentTokens((Comment) oldValue, nodeText);
                        int index = indexAndCount.a;
                        for (int i = 0; i < indexAndCount.b; i++) {
                            nodeText.removeElement(index);
                        }
                        if (isCompleteLine(nodeText.getElements(), index)) {
                            removeAllExtraCharacters(nodeText.getElements(), index);
                        } else {
                            removeAllExtraCharactersStartingFrom(
                                    nodeText.getElements().listIterator(index));
                        }
                    } else {
                        throw new UnsupportedOperationException("Trying to remove something that is not a comment!");
                    }
                } else {
                    // this is a replacement of a comment
                    List<TokenTextElement> matchingTokens =
                            findTokenTextElementForComment((Comment) oldValue, nodeText);
                    if ((oldValue instanceof MarkdownComment && matchingTokens.isEmpty())
                            || (!(oldValue instanceof MarkdownComment) && matchingTokens.size() != 1)) {
                        throw new IllegalStateException("The matching comment to be replaced could not be found");
                    }
                    Comment newComment = (Comment) newValue;
                    TokenTextElement firstMatchingElement = matchingTokens.get(0);
                    int index = nodeText.findElement(firstMatchingElement.and(firstMatchingElement.matchByRange()));
                    // When replacing a MarkdownComment, all matching tokens must be removed before adding new ones
                    for (int i = 0; i < matchingTokens.size(); i++) {
                        nodeText.removeElement(index);
                    }
                    for (TokenTextElement newElement : makeCommentTokens(newComment)) {
                        nodeText.addElement(index++, newElement);
                    }
                }
            }
            NodeText nodeText = getOrCreateNodeText(observedNode);
            if (nodeText == null) {
                throw new NullPointerException(observedNode.getClass().getSimpleName());
            }
            LEXICAL_DIFFERENCE_CALCULATOR.calculatePropertyChange(nodeText, observedNode, property, oldValue, newValue);
        }

        private boolean isCompleteLine(List<TextElement> elements, int index) {
            if (index <= 0 || index >= elements.size()) return false;
            boolean isCompleteLine = true;
            ListIterator<TextElement> iterator = elements.listIterator(index);
            // verify if elements after the index are only spaces or tabs
            while (iterator.hasNext()) {
                TextElement textElement = iterator.next();
                if (textElement.isNewline()) break;
                if (textElement.isSpaceOrTab()) continue;
                isCompleteLine = false;
                break;
            }
            // verify if elements before the index are only spaces or tabs
            iterator = elements.listIterator(index);
            while (iterator.hasPrevious() && isCompleteLine) {
                TextElement textElement = iterator.previous();
                if (textElement.isNewline()) break;
                if (textElement.isSpaceOrTab()) continue;
                isCompleteLine = false;
            }
            return isCompleteLine;
        }

        private void removeAllExtraCharacters(List<TextElement> elements, int index) {
            if (index < 0 || index >= elements.size()) return;
            removeAllExtraCharactersStartingFrom(elements.listIterator(index));
            removeAllExtraCharactersBeforePosition(elements.listIterator(index));
        }

        /*
         * Removes all spaces,tabs characters before this position
         */
        private void removeAllExtraCharactersBeforePosition(ListIterator<TextElement> iterator) {
            while (iterator.hasPrevious()) {
                TextElement textElement = iterator.previous();
                if (textElement.isSpaceOrTab()) {
                    iterator.remove();
                    continue;
                }
                break;
            }
        }

        /*
         * Removes all spaces,tabs or new line characters starting from this position
         */
        private void removeAllExtraCharactersStartingFrom(ListIterator<TextElement> iterator) {
            while (iterator.hasNext()) {
                TextElement textElement = iterator.next();
                if (textElement.isSpaceOrTab()) {
                    iterator.remove();
                    continue;
                }
                if (textElement.isNewline()) {
                    iterator.remove();
                }
                break;
            }
        }

        private List<TokenTextElement> convertMarkdownCommentContentToTokens(MarkdownComment comment) {
            ArrayList<TokenTextElement> tokens = new ArrayList<>();
            String content = comment.getContent();
            for (int i = 0; i < content.length(); i++) {
                if (content.charAt(i) == '/') {
                    int commentStart = i;
                    while (i < content.length() - 1) {
                        if (content.charAt(i + 1) == '\n' || content.charAt(i + 1) == '\r') {
                            break;
                        }
                        i++;
                    }
                    tokens.add(new TokenTextElement(SINGLE_LINE_COMMENT, content.substring(commentStart, i + 1)));
                } else if (content.charAt(i) == '\r') {
                    if (i < content.length() - 1 && content.charAt(i + 1) == '\n') {
                        tokens.add(new TokenTextElement(SPACE, "\r\n"));
                        i++;
                    } else {
                        tokens.add(new TokenTextElement(SPACE, "\r"));
                    }
                } else if (Character.isWhitespace(content.charAt(i))) {
                    tokens.add(new TokenTextElement(SPACE, Character.toString(content.charAt(i))));
                } else {
                    throw new IllegalArgumentException("Expected Markdown comment content format, but got " + comment);
                }
            }
            return tokens;
        }

        private List<TokenTextElement> makeCommentTokens(Comment newComment) {
            List<TokenTextElement> tokens = new ArrayList<>();
            if (newComment.isJavadocComment()) {
                TokenTextElement t = new TokenTextElement(
                        JAVADOC_COMMENT, newComment.getHeader() + newComment.getContent() + newComment.getFooter());
                tokens.add(t);
            } else if (newComment.isLineComment()) {
                TokenTextElement t =
                        new TokenTextElement(SINGLE_LINE_COMMENT, newComment.getHeader() + newComment.getContent());
                tokens.add(t);
            } else if (newComment.isBlockComment()) {
                TokenTextElement t = new TokenTextElement(
                        MULTI_LINE_COMMENT, newComment.getHeader() + newComment.getContent() + newComment.getFooter());
                tokens.add(t);
            } else if (newComment.isMarkdownComment()) {
                // TODO construct token list
                // String[] lines = newComment.getContent().split("\\R");
                // for (String line : newComment.getContent().split("\\R")) {
                //     for (int i = 0; i < line.length(); i++) {
                //         if (line.charAt(i) == '/') {
                //             TokenTextElement t = new TokenTextElement(SINGLE_LINE_COMMENT, line.substring(i));
                //             tokens.add(t);
                //             break;
                //         } else {
                //             tokens.add(new TokenTextElement(SPACE, Character.toString(line.charAt(i))));
                //         }
                //     }
                // }
                tokens.addAll(convertMarkdownCommentContentToTokens(newComment.asMarkdownComment()));
            } else {
                throw new UnsupportedOperationException(
                        "Unknown type of comment: " + newComment.getClass().getSimpleName());
            }
            return tokens;
        }

        private Pair<Integer, Integer> getIndexAndCountOfCommentTokens(Comment oldValue, NodeText nodeText) {
            List<TokenTextElement> matchingTokens = findTokenTextElementForComment(oldValue, nodeText);
            if (!matchingTokens.isEmpty()) {
                TextElement matchingElement = matchingTokens.get(0);
                return new Pair<>(
                        nodeText.findElement(matchingElement.and(matchingElement.matchByRange())),
                        matchingTokens.size());
            }
            // If no matching TokenTextElements were found, we try searching through ChildTextElements as well
            List<ChildTextElement> matchingChilds = findChildTextElementForComment(oldValue, nodeText);
            ChildTextElement matchingChild = matchingChilds.get(0);
            return new Pair<>(
                    nodeText.findElement(matchingChild.and(matchingChild.matchByRange())), matchingChilds.size());
        }

        /*
         * Comment
         */
        private List<ChildTextElement> findChildTextElementForComment(Comment oldValue, NodeText nodeText) {
            List<ChildTextElement> matchingChildElements;
            matchingChildElements = selectMatchingChildElements(oldValue, nodeText);
            if (matchingChildElements.size() > 1) {
                // Duplicate child nodes found, refine the result
                matchingChildElements = matchingChildElements.stream()
                        .filter(t -> t.getChild().hasRange() && oldValue.hasRange())
                        .filter(t -> t.getChild()
                                        .getRange()
                                        .get()
                                        .equals(oldValue.getRange().get())
                                || (t.getChild().getComment().isPresent()
                                        && t.getChild().getComment().get().hasRange()
                                        && t.getChild()
                                                .getComment()
                                                .get()
                                                .getRange()
                                                .get()
                                                .equals(oldValue.getRange().get())))
                        .collect(toList());
            }
            if (matchingChildElements.size() != 1) {
                throw new IllegalStateException(
                        "The matching child text element for the comment to be removed could not be found.");
            }
            return matchingChildElements;
        }

        private List<ChildTextElement> selectMatchingChildElements(Comment oldValue, NodeText nodeText) {
            List<ChildTextElement> result = new ArrayList<>();
            List<ChildTextElement> childTextElements = nodeText.getElements().stream()
                    .filter(e -> e.isChild())
                    .map(c -> (ChildTextElement) c)
                    .collect(toList());
            ListIterator<ChildTextElement> iterator = childTextElements.listIterator();
            while (iterator.hasNext()) {
                ChildTextElement textElement = iterator.next();
                if (textElement.isComment() && isSameComment(((Comment) textElement.getChild()), oldValue)) {
                    result.add(textElement);
                    continue;
                }
                Node node = textElement.getChild();
                if (node.getComment().isPresent()
                        && isSameComment(node.getComment().get(), oldValue)) {
                    result.add(textElement);
                    continue;
                }
            }
            return result;
        }

        private boolean isSameComment(Comment childValue, Comment oldValue) {
            return childValue.getContent().equals(oldValue.getContent());
        }

        private List<TokenTextElement> findTokenTextElementForComment(Comment oldValue, NodeText nodeText) {
            List<TokenTextElement> matchingTokens;
            if (oldValue instanceof TraditionalJavadocComment) {
                matchingTokens = nodeText.getElements().stream()
                        .filter(e -> e.isToken(JAVADOC_COMMENT))
                        .map(e -> (TokenTextElement) e)
                        .filter(t -> t.getText().equals(oldValue.asString()))
                        .collect(toList());
            } else if (oldValue instanceof BlockComment) {
                matchingTokens = nodeText.getElements().stream()
                        .filter(e -> e.isToken(MULTI_LINE_COMMENT))
                        .map(e -> (TokenTextElement) e)
                        .filter(t -> t.getText().equals(oldValue.asString()))
                        .collect(toList());
            } else if (oldValue instanceof MarkdownComment) {
                matchingTokens = new ArrayList<>();
                ArrayList<TextElement> maybeMatchingTokens = new ArrayList<>();
                boolean inMatch = false;
                String oldContent = oldValue.asMarkdownComment().getContent();
                List<TextElement> textElements = nodeText.getElements();
                for (TextElement textElement : textElements) {
                    if (inMatch) {
                        maybeMatchingTokens.add(textElement);
                        if (textElement.isToken(SINGLE_LINE_COMMENT) && oldContent.endsWith(textElement.expand())) {
                            // We have a matching start and end, so check that the full text matches.
                            StringBuilder sb = new StringBuilder();
                            for (TextElement elem : maybeMatchingTokens) {
                                sb.append(((TokenTextElement) elem).getText());
                            }
                            if (sb.toString().equals(oldContent)) {
                                matchingTokens.addAll(maybeMatchingTokens.stream()
                                        .map(e -> (TokenTextElement) e)
                                        .collect(toList()));
                                // Clear and continue, since multiple markdown comments may have the same content
                                maybeMatchingTokens.clear();
                                inMatch = false;
                            } else {
                                maybeMatchingTokens.clear();
                                inMatch = false;
                            }
                        }
                    } else if (textElement.isToken(SINGLE_LINE_COMMENT)
                            && oldContent.startsWith(((TokenTextElement) textElement).getText())) {
                        maybeMatchingTokens.add(textElement);
                        inMatch = true;
                    }
                }
            } else {
                matchingTokens = nodeText.getElements().stream()
                        .filter(e -> e.isToken(SINGLE_LINE_COMMENT))
                        .map(e -> (TokenTextElement) e)
                        .filter(t -> t.getText().trim().equals((oldValue.asString()).trim()))
                        .collect(toList());
            }
            // To check that a comment matches in the list of tokens, if exists the range must be always checked,
            // as comments with the same content may exist on different lines.
            return matchingTokens.stream()
                    .filter(t -> (!t.getToken().hasRange() && !oldValue.hasRange())
                            || (t.getToken().hasRange()
                                    && oldValue.hasRange()
                                    && oldValue.getRange()
                                            .get()
                                            .contains(t.getToken().getRange().get())))
                    .collect(toList());
        }

        /**
         * This method inserts new space tokens at the given {@code index}. If a new
         * comment is added to the token list at the position following {@code index},
         * the new comment and the node will have the same indent.
         *
         * @param nodeText The text of the node
         * @param index    The position at which the analysis should start
         */
        private void fixIndentOfAddedNode(NodeText nodeText, int index) {
            if (index <= 0) {
                return;
            }
            TextElement currentSpaceCandidate = null;
            for (int i = index; i >= 0; i--) {
                TextElement spaceCandidate = nodeText.getTextElement(i);
                if (spaceCandidate.isSpaceOrTab()) {
                    // save the current indentation char
                    currentSpaceCandidate = nodeText.getTextElement(i);
                }
                if (!spaceCandidate.isSpaceOrTab()) {
                    if (spaceCandidate.isNewline() && i != index) {
                        int numberOfIndentationCharacters = index - i;
                        for (int j = 0; j < numberOfIndentationCharacters; j++) {
                            if (currentSpaceCandidate != null) {
                                // use the current (or last) indentation character
                                nodeText.addElement(
                                        index,
                                        new TokenTextElement(
                                                JavaToken.Kind.SPACE.getKind(), currentSpaceCandidate.expand()));
                            } else {
                                // use the default indentation character
                                nodeText.addElement(index, new TokenTextElement(JavaToken.Kind.SPACE.getKind()));
                            }
                        }
                    }
                    break;
                }
            }
        }

        @Override
        public void concreteListChange(
                NodeList<?> changedList, ListChangeType type, int index, Node nodeAddedOrRemoved) {
            NodeText nodeText = getOrCreateNodeText(changedList.getParentNodeForChildren());
            final List<DifferenceElement> differenceElements;
            if (type == AstObserver.ListChangeType.REMOVAL) {
                differenceElements = LEXICAL_DIFFERENCE_CALCULATOR.calculateListRemovalDifference(
                        findNodeListName(changedList), changedList, index);
            } else if (type == AstObserver.ListChangeType.ADDITION) {
                differenceElements = LEXICAL_DIFFERENCE_CALCULATOR.calculateListAdditionDifference(
                        findNodeListName(changedList), changedList, index, nodeAddedOrRemoved);
            } else {
                throw new UnsupportedOperationException("Unknown change type: " + type);
            }
            Difference difference =
                    new Difference(differenceElements, nodeText, changedList.getParentNodeForChildren());
            difference.apply();
        }

        @Override
        public void concreteListReplacement(NodeList<?> changedList, int index, Node oldValue, Node newValue) {
            NodeText nodeText = getOrCreateNodeText(changedList.getParentNodeForChildren());
            List<DifferenceElement> differenceElements =
                    LEXICAL_DIFFERENCE_CALCULATOR.calculateListReplacementDifference(
                            findNodeListName(changedList), changedList, index, newValue);
            Difference difference =
                    new Difference(differenceElements, nodeText, changedList.getParentNodeForChildren());
            difference.apply();
        }
    }

    /**
     * Stores the initial textual representation for all nodes in the AST.
     * This method creates a NodeText object for each node that captures:
     * - The original tokens associated with the node
     * - Whitespace and formatting information
     * - Comment associations
     * - Token positions and relationships
     *
     * This initial storage is crucial for later determining what has changed
     * and what should be preserved during printing.
     *
     * @param cu The root node to process
     */
    private static void storeInitialText(Node root) {
        Map<Node, List<JavaToken>> tokensByNode = new IdentityHashMap<>();
        // We go over tokens and find to which nodes they belong. Note that we do not traverse the tokens as they were
        // on a list but as they were organized in a tree. At each time we select only the branch corresponding to the
        // range of interest and ignore all other branches
        root.getTokenRange().ifPresent(rootTokenRange -> {
            for (JavaToken token : rootTokenRange) {
                Range tokenRange =
                        token.getRange().orElseThrow(() -> new RuntimeException("Token without range: " + token));
                Node owner = root.findByRange(tokenRange)
                        .orElseThrow(() -> new RuntimeException("Token without node owning it: " + token));
                if (!tokensByNode.containsKey(owner)) {
                    tokensByNode.put(owner, new LinkedList<>());
                }
                tokensByNode.get(owner).add(token);
            }
            // Now that we know the tokens we use them to create the initial NodeText for each node
            new TreeVisitor() {

                @Override
                public void process(Node node) {
                    if (!node.isPhantom()) {
                        storeInitialTextForOneNode(node, tokensByNode.get(node));
                    }
                }
            }.visitBreadthFirst(root);
        });
    }

    /**
     * Recursively stores initial text representation for all child nodes
     * of the given parent node.
     *
     * This method ensures that every node in the AST has its original
     * textual representation captured for lexical preservation.
     *
     * @param node The parent node whose children should be processed
     */
    private static void storeInitialTextForOneNode(Node node, List<JavaToken> nodeTokens) {
        if (nodeTokens == null) {
            nodeTokens = Collections.emptyList();
        }
        List<Pair<Range, TextElement>> elements = new LinkedList<>();
        for (Node child : node.getChildNodes()) {
            if (!child.isPhantom()) {
                if (!child.hasRange()) {
                    throw new RuntimeException("Range not present on node " + child);
                }
                elements.add(new Pair<>(child.getRange().get(), new ChildTextElement(child)));
            }
        }
        for (JavaToken token : nodeTokens) {
            elements.add(new Pair<>(token.getRange().get(), new TokenTextElement(token)));
        }
        elements.sort(comparing(e -> e.a.begin));
        node.setData(
                NODE_TEXT_DATA, new NodeText(elements.stream().map(p -> p.b).collect(toList())));
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
            }
            return new TextElementIteratorsFactory.EmptyIterator<TokenTextElement>();
        }
        return new TextElementIteratorsFactory.CascadingIterator<>(
                TextElementIteratorsFactory.partialReverseIterator(parentNodeText, index - 1),
                () -> tokensPreceeding(node.getParentNode().get()));
    }

    //
    // Printing methods
    //
    /**
     * Prints the given node to a string while preserving the original formatting
     * where possible and applying changes where the AST has been modified.
     *
     * This method analyzes the changes made to the AST since lexical preservation
     * was setup and generates output that:
     * - Preserves original formatting for unchanged portions
     * - Applies appropriate formatting for new or modified content
     * - Maintains consistency with the original code style
     *
     * @param node The node to print (typically a CompilationUnit)
     * @return A string representation of the node with preserved formatting
     */
    public static String print(Node node) {
        Printer printer = new DefaultLexicalPreservingPrinter();
        return printer.print(node);
    }

    //
    // Methods to handle transformations
    //
    private static void prettyPrintingTextNode(Node node, NodeText nodeText) {
        if (node instanceof PrimitiveType) {
            interpret(node, ConcreteSyntaxModel.forClass(node.getClass()), nodeText);
            return;
        }
        if (node instanceof TraditionalJavadocComment) {
            Comment comment = (TraditionalJavadocComment) node;
            nodeText.addToken(
                    JAVADOC_COMMENT,
                    comment.getHeader() + ((TraditionalJavadocComment) node).getContent() + comment.getFooter());
            return;
        }
        if (node instanceof BlockComment) {
            Comment comment = (BlockComment) node;
            nodeText.addToken(
                    MULTI_LINE_COMMENT, comment.getHeader() + ((BlockComment) node).getContent() + comment.getFooter());
            return;
        }
        if (node instanceof LineComment) {
            Comment comment = (LineComment) node;
            nodeText.addToken(SINGLE_LINE_COMMENT, comment.getHeader() + comment.getContent());
            return;
        }
        if (node instanceof Modifier) {
            Modifier modifier = (Modifier) node;
            nodeText.addToken(
                    LexicalDifferenceCalculator.toToken(modifier),
                    modifier.getKeyword().asString());
            return;
        }
        interpret(node, ConcreteSyntaxModel.forClass(node.getClass()), nodeText);
    }

    /**
     * TODO: Process CsmIndent and CsmUnindent before reaching this point
     */
    private static NodeText interpret(Node node, CsmElement csm, NodeText nodeText) {
        LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel =
                new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(csm, node);
        List<TextElement> indentation = findIndentation(node);
        boolean pendingIndentation = false;
        // Add a comment and line separator if necessary
        node.getComment().ifPresent(comment -> {
            // new comment has no range so in this case we want to force the comment before the node
            if (!comment.hasRange()) {
                LineSeparator lineSeparator = node.getLineEndingStyleOrDefault(LineSeparator.SYSTEM);
                calculatedSyntaxModel.elements.add(
                        0, new CsmToken(eolTokenKind(lineSeparator), lineSeparator.asRawString()));
                calculatedSyntaxModel.elements.add(0, new CsmChild(comment));
            }
        });
        for (CsmElement element : calculatedSyntaxModel.elements) {
            if (element instanceof CsmIndent) {
                int indexCurrentElement = calculatedSyntaxModel.elements.indexOf(element);
                if (calculatedSyntaxModel.elements.size() > indexCurrentElement
                        && !(calculatedSyntaxModel.elements.get(indexCurrentElement + 1) instanceof CsmUnindent)) {
                    for (int i = 0; i < Difference.STANDARD_INDENTATION_SIZE; i++) {
                        indentation.add(new TokenTextElement(SPACE, " "));
                    }
                }
            } else if (element instanceof CsmUnindent) {
                for (int i = 0; i < Difference.STANDARD_INDENTATION_SIZE && indentation.size() > 0; i++) {
                    indentation.remove(indentation.size() - 1);
                }
            }
            if (pendingIndentation && !(element instanceof CsmToken && ((CsmToken) element).isNewLine())) {
                indentation.forEach(nodeText::addElement);
            }
            pendingIndentation = false;
            if (element instanceof LexicalDifferenceCalculator.CsmChild) {
                nodeText.addChild(((LexicalDifferenceCalculator.CsmChild) element).getChild());
            } else if (element instanceof CsmToken) {
                CsmToken csmToken = (CsmToken) element;
                nodeText.addToken(csmToken.getTokenType(), csmToken.getContent());
                if (csmToken.isNewLine()) {
                    pendingIndentation = true;
                }
            } else if (element instanceof CsmMix) {
                CsmMix csmMix = (CsmMix) element;
                csmMix.getElements().forEach(e -> interpret(node, e, nodeText));
            } else {
                // Indentation should probably be dealt with before because an indentation has effects also on the
                // following lines
                if (!(element instanceof CsmIndent) && !(element instanceof CsmUnindent)) {
                    throw new UnsupportedOperationException(
                            "Unknown element type: " + element.getClass().getSimpleName());
                }
            }
        }
        // Array brackets are a pain... we do not have a way to represent them explicitly in the AST
        // so they have to be handled in a special way
        if (node instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator) node;
            variableDeclarator.getParentNode().ifPresent(parent -> ((NodeWithVariables<?>) parent)
                    .getMaximumCommonType()
                    .ifPresent(mct -> {
                        int extraArrayLevels = variableDeclarator.getType().getArrayLevel() - mct.getArrayLevel();
                        for (int i = 0; i < extraArrayLevels; i++) {
                            nodeText.addElement(new TokenTextElement(LBRACKET));
                            nodeText.addElement(new TokenTextElement(RBRACKET));
                        }
                    }));
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
    static List<TextElement> findIndentation(Node node) {
        List<TextElement> followingNewlines = new LinkedList<>();
        Iterator<TokenTextElement> it = tokensPreceeding(node);
        while (it.hasNext()) {
            TokenTextElement tte = it.next();
            if (tte.getTokenKind() == SINGLE_LINE_COMMENT || tte.isNewline()) {
                break;
            }
            followingNewlines.add(tte);
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
        if (!m.getReturnType().getCanonicalName().equals(JAVA_UTIL_OPTIONAL)) {
            return false;
        }
        if (!(m.getGenericReturnType() instanceof ParameterizedType)) {
            return false;
        }
        ParameterizedType parameterizedType = (ParameterizedType) m.getGenericReturnType();
        java.lang.reflect.Type optionalArgument = parameterizedType.getActualTypeArguments()[0];
        return (optionalArgument.getTypeName().startsWith(JAVAPARSER_AST_NODELIST));
    }

    private static ObservableProperty findNodeListName(NodeList<?> nodeList) {
        Node parent = nodeList.getParentNodeForChildren();
        for (Method m : parent.getClass().getMethods()) {
            if (m.getParameterCount() == 0
                    && m.getReturnType().getCanonicalName().equals(JAVAPARSER_AST_NODELIST)) {
                try {
                    Object raw = m.invoke(parent);
                    if (!(raw instanceof NodeList)) {
                        throw new IllegalStateException(
                                "Expected NodeList, found " + raw.getClass().getCanonicalName());
                    }
                    NodeList<?> result = (NodeList<?>) raw;
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
