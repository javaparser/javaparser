/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.JavaToken;
import com.github.javaparser.Range;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import com.github.javaparser.utils.LineSeparator;
import com.github.javaparser.utils.Pair;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.util.*;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.decapitalize;
import static java.util.Comparator.comparing;
import static java.util.stream.Collectors.toList;

/**
 * A Lexical Preserving Printer is used to capture all the lexical information while parsing, update them when
 * operating on the AST and then used them to reproduce the source code
 * in its original formatting including the AST changes.
 */
public class LexicalPreservingPrinter {

    private static String JAVA_UTIL_OPTIONAL = Optional.class.getCanonicalName();

    private static String JAVAPARSER_AST_NODELIST = NodeList.class.getCanonicalName();

    private static AstObserver observer;

    /**
     * The nodetext for a node is stored in the node's data field. This is the key to set and retrieve it.
     */
    public static final DataKey<NodeText> NODE_TEXT_DATA = new DataKey<NodeText>() {
    };

    private static final LexicalDifferenceCalculator LEXICAL_DIFFERENCE_CALCULATOR = new LexicalDifferenceCalculator();

    // 
    // Factory methods
    // 
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
        public void concretePropertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
            if (oldValue == newValue) {
                // Not really a change, ignore
                return;
            }
            if (property == ObservableProperty.RANGE || property == ObservableProperty.COMMENTED_NODE) {
                return;
            }
            if (property == ObservableProperty.COMMENT) {
                Optional<Node> parentNode = observedNode.getParentNode();
                NodeText nodeText = parentNode.map(parent -> getOrCreateNodeText(parentNode.get())).// We're at the root node.
                orElse(getOrCreateNodeText(observedNode));
                if (oldValue == null) { // this case corresponds to the addition of a comment
                    int index = parentNode.isPresent() ? // Find the position of the comment node and put in front of it the [...]
                    nodeText.findChild(observedNode) : // 
                    0;
                    // Add the same indent depth of the comment to the following node
                    fixIndentOfMovedNode(nodeText, index);
                    LineSeparator lineSeparator = observedNode.getLineEndingStyleOrDefault(LineSeparator.SYSTEM);
                    nodeText.addElement(index, makeCommentToken((Comment) newValue));
                    nodeText.addToken(index + 1, eolTokenKind(lineSeparator), lineSeparator.asRawString());
                } else if (newValue == null) { // this case corresponds to a deletion of a comment
                    if (oldValue instanceof Comment) {
                        if (((Comment) oldValue).isOrphan()) {
                            nodeText = getOrCreateNodeText(observedNode);
                        }
                        int index = getIndexOfComment((Comment) oldValue, nodeText);
                        nodeText.removeElement(index);
                        if (isCompleteLine(nodeText.getElements(), index)) {
                        	removeAllExtraCharacters(nodeText.getElements(), index);
                        } else {
                        	removeAllExtraCharactersStartingFrom(nodeText.getElements().listIterator(index));
                        }
//                        if (nodeText.getElements().get(index).isNewline()) {
//                            nodeText.removeElement(index);
//                        }
                    } else {
                        throw new UnsupportedOperationException("Trying to remove something that is not a comment!");
                    }
                } else {
                    List<TokenTextElement> matchingTokens = findTokenTextElementForComment((Comment) oldValue, nodeText);
                    if (matchingTokens.size() != 1) {
                        throw new IllegalStateException("The matching comment to be replaced could not be found");
                    }
                    Comment newComment = (Comment) newValue;
                    TokenTextElement matchingElement = matchingTokens.get(0);
                    nodeText.replace(matchingElement.and(matchingElement.matchByRange()), makeCommentToken(newComment));
                }
            }
            NodeText nodeText = getOrCreateNodeText(observedNode);
            if (nodeText == null) {
                throw new NullPointerException(observedNode.getClass().getSimpleName());
            }
            LEXICAL_DIFFERENCE_CALCULATOR.calculatePropertyChange(nodeText, observedNode, property, oldValue, newValue);
        }
        
        private boolean isCompleteLine(List<TextElement> elements , int index) {
        	if (index <= 0 || index >= elements.size()) return false;
        	boolean isCompleteLine=true;
        	ListIterator<TextElement> iterator = elements.listIterator(index);
        	// verify if elements after the index are only spaces or tabs 
        	while(iterator.hasNext()) {
        		TextElement textElement = iterator.next();
        		if (textElement.isNewline()) break;
        		if (textElement.isSpaceOrTab()) continue;
        		isCompleteLine=false;
        		break;
        	}
        	// verify if elements before the index are only spaces or tabs 
        	iterator = elements.listIterator(index);
        	while(iterator.hasPrevious() && isCompleteLine) {
        		TextElement textElement = iterator.previous();
        		if (textElement.isNewline()) break;
        		if (textElement.isSpaceOrTab()) continue;
        		isCompleteLine=false;
        	}
        	
        	return isCompleteLine;
        }
        
        private void removeAllExtraCharacters(List<TextElement> elements , int index) {
        	if (index < 0 || index >= elements.size()) return;
        	removeAllExtraCharactersStartingFrom(elements.listIterator(index));
        	removeAllExtraCharactersBeforePosition(elements.listIterator(index));
        }

        /*
         * Removes all spaces,tabs characters before this position
         */
		private void removeAllExtraCharactersBeforePosition(ListIterator<TextElement> iterator) {
        	while(iterator.hasPrevious()) {
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
        	while(iterator.hasNext()) {
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
        
        private TokenTextElement makeCommentToken(Comment newComment) {
            if (newComment.isJavadocComment()) {
                return new TokenTextElement(JAVADOC_COMMENT, "/**" + newComment.getContent() + "*/");
            }
            if (newComment.isLineComment()) {
                return new TokenTextElement(SINGLE_LINE_COMMENT, "//" + newComment.getContent());
            }
            if (newComment.isBlockComment()) {
                return new TokenTextElement(MULTI_LINE_COMMENT, "/*" + newComment.getContent() + "*/");
            }
            throw new UnsupportedOperationException("Unknown type of comment: " + newComment.getClass().getSimpleName());
        }

        private int getIndexOfComment(Comment oldValue, NodeText nodeText) {
            List<TokenTextElement> matchingTokens = findTokenTextElementForComment(oldValue, nodeText);
            if (!matchingTokens.isEmpty()) {
                TextElement matchingElement = matchingTokens.get(0);
                return nodeText.findElement(matchingElement.and(matchingElement.matchByRange()));
            }
            // If no matching TokenTextElements were found, we try searching through ChildTextElements as well
            List<ChildTextElement> matchingChilds = findChildTextElementForComment(oldValue, nodeText);
            ChildTextElement matchingChild = matchingChilds.get(0);
            return nodeText.findElement(matchingChild.and(matchingChild.matchByRange()));
        }

        private List<ChildTextElement> findChildTextElementForComment(Comment oldValue, NodeText nodeText) {
            List<ChildTextElement> matchingChildElements;
			matchingChildElements = selectMatchingChildElements(oldValue, nodeText);
            if (matchingChildElements.size() > 1) {
                // Duplicate child nodes found, refine the result
                matchingChildElements = matchingChildElements.stream().filter(t -> isEqualRange(t.getChild().getRange(), oldValue.getRange())).collect(toList());
            }
            if (matchingChildElements.size() != 1) {
                throw new IllegalStateException("The matching child text element for the comment to be removed could not be found.");
            }
            return matchingChildElements;
        }
        
        private List<ChildTextElement> selectMatchingChildElements(Comment oldValue, NodeText nodeText) {
        	List<ChildTextElement> result = new ArrayList<>();
        	List<ChildTextElement> childTextElements = nodeText.getElements().stream().filter(e -> e.isChild())
					.map(c -> (ChildTextElement) c).collect(toList());
        	ListIterator<ChildTextElement> iterator = childTextElements.listIterator();
        	while(iterator.hasNext()) {
        		ChildTextElement textElement = iterator.next();
        		if (textElement.isComment() && isSameComment(((Comment) textElement.getChild()), oldValue)) {
        			result.add(textElement);
        			continue;
        		}
        		Node node = textElement.getChild();
        		if (node.getComment().isPresent() && isSameComment(node.getComment().get(), oldValue)) {
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
            if (oldValue instanceof JavadocComment) {
                matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(JAVADOC_COMMENT)).map(e -> (TokenTextElement) e).filter(t -> t.getText().equals("/**" + oldValue.getContent() + "*/")).collect(toList());
            } else if (oldValue instanceof BlockComment) {
                matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(MULTI_LINE_COMMENT)).map(e -> (TokenTextElement) e).filter(t -> t.getText().equals("/*" + oldValue.getContent() + "*/")).collect(toList());
            } else {
                matchingTokens = nodeText.getElements().stream().filter(e -> e.isToken(SINGLE_LINE_COMMENT)).map(e -> (TokenTextElement) e).filter(t -> t.getText().trim().equals(("//" + oldValue.getContent()).trim())).collect(toList());
            }
            if (matchingTokens.size() > 1) {
                // Duplicate comments found, refine the result
                matchingTokens = matchingTokens.stream().filter(t -> isEqualRange(t.getToken().getRange(), oldValue.getRange())).collect(toList());
            }
            return matchingTokens;
        }

        private boolean isEqualRange(Optional<Range> range1, Optional<Range> range2) {
            if (range1.isPresent() && range2.isPresent()) {
                return range1.get().equals(range2.get());
            }
            return false;
        }

        /**
         * This method inserts new space tokens at the given {@code index}. If a new comment is added to the node
         * at the position of {@code index}, the new comment and the node will have the same indent.
         *
         * @param nodeText The text of the node
         * @param index    The position where a new comment will be added to
         */
        private void fixIndentOfMovedNode(NodeText nodeText, int index) {
            if (index <= 0) {
                return;
            }
            TextElement currentSpaceCandidate = null;
            for (int i = index - 1; i >= 0; i--) {
                TextElement spaceCandidate = nodeText.getTextElement(i);
                if (spaceCandidate.isSpaceOrTab()) {
                    // save the current indentation char
                    currentSpaceCandidate = nodeText.getTextElement(i);
                }
                if (!spaceCandidate.isSpaceOrTab()) {
                    if (spaceCandidate.isNewline() && i != index - 1) {
                        for (int j = 0; j < (index - 1) - i; j++) {
                            if (currentSpaceCandidate != null) {
                                // use the current (or last) indentation character
                                nodeText.addElement(index, new TokenTextElement(JavaToken.Kind.SPACE.getKind(), currentSpaceCandidate.expand()));
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
        public void concreteListChange(NodeList<?> changedList, ListChangeType type, int index, Node nodeAddedOrRemoved) {
            NodeText nodeText = getOrCreateNodeText(changedList.getParentNodeForChildren());
            final List<DifferenceElement> differenceElements;
            if (type == AstObserver.ListChangeType.REMOVAL) {
                differenceElements = LEXICAL_DIFFERENCE_CALCULATOR.calculateListRemovalDifference(findNodeListName(changedList), changedList, index);
            } else if (type == AstObserver.ListChangeType.ADDITION) {
                differenceElements = LEXICAL_DIFFERENCE_CALCULATOR.calculateListAdditionDifference(findNodeListName(changedList), changedList, index, nodeAddedOrRemoved);
            } else {
                throw new UnsupportedOperationException();
            }
            Difference difference = new Difference(differenceElements, nodeText, changedList.getParentNodeForChildren());
            difference.apply();
        }

        @Override
        public void concreteListReplacement(NodeList<?> changedList, int index, Node oldValue, Node newValue) {
            NodeText nodeText = getOrCreateNodeText(changedList.getParentNodeForChildren());
            List<DifferenceElement> differenceElements = LEXICAL_DIFFERENCE_CALCULATOR.calculateListReplacementDifference(findNodeListName(changedList), changedList, index, newValue);
            Difference difference = new Difference(differenceElements, nodeText, changedList.getParentNodeForChildren());
            difference.apply();
        }
    }

    private static void storeInitialText(Node root) {
        Map<Node, List<JavaToken>> tokensByNode = new IdentityHashMap<>();
        // We go over tokens and find to which nodes they belong. Note that we do not traverse the tokens as they were
        // on a list but as they were organized in a tree. At each time we select only the branch corresponding to the
        // range of interest and ignore all other branches
        root.getTokenRange().ifPresent(rootTokenRange -> {
            for (JavaToken token : rootTokenRange) {
                Range tokenRange = token.getRange().orElseThrow(() -> new RuntimeException("Token without range: " + token));
                Node owner = findNodeForToken(root, tokenRange).orElseThrow(() -> new RuntimeException("Token without node owning it: " + token));
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
                        LexicalPreservingPrinter.storeInitialTextForOneNode(node, tokensByNode.get(node));
                    }
                }
            }.visitBreadthFirst(root);
        });
    }

    private static Optional<Node> findNodeForToken(Node node, Range tokenRange) {
        if (node.isPhantom()) {
            return Optional.empty();
        }
        if (!node.hasRange()) {
            return Optional.empty();
        }
        if (!node.getRange().get().contains(tokenRange)) {
            return Optional.empty();
        }
        for (Node child : node.getChildNodes()) {
            Optional<Node> found = findNodeForToken(child, tokenRange);
            if (found.isPresent()) {
                return found;
            }
        }
        return Optional.of(node);
    }

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
        node.setData(NODE_TEXT_DATA, new NodeText(elements.stream().map(p -> p.b).collect(toList())));
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
            	// comment node can be removed at this stage.
            	return new TextElementIteratorsFactory.EmptyIterator<TokenTextElement>();
//                throw new IllegalArgumentException(String.format("I could not find child '%s' in parent '%s'. parentNodeText: %s", node, node.getParentNode().get(), parentNodeText));
            }
        }
        return new TextElementIteratorsFactory.CascadingIterator<>(TextElementIteratorsFactory.partialReverseIterator(parentNodeText, index - 1), () -> tokensPreceeding(node.getParentNode().get()));
    }

    // 
    // Printing methods
    // 
    /**
     * Print a Node into a String, preserving the lexical information.
     */
    public static String print(Node node) {
    	LexicalPreservingVisitor visitor = new LexicalPreservingVisitor();
    	final NodeText nodeText = getOrCreateNodeText(node);
    	nodeText.getElements().forEach(element -> element.accept(visitor));
        return visitor.toString();
																					  
    }

    // 
    // Methods to handle transformations
    // 
    private static void prettyPrintingTextNode(Node node, NodeText nodeText) {
        if (node instanceof PrimitiveType) {
            PrimitiveType primitiveType = (PrimitiveType) node;
            switch(primitiveType.getType()) {
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
        if (node instanceof BlockComment) {
            nodeText.addToken(MULTI_LINE_COMMENT, "/*" + ((BlockComment) node).getContent() + "*/");
            return;
        }
        if (node instanceof LineComment) {
            nodeText.addToken(SINGLE_LINE_COMMENT, "//" + ((LineComment) node).getContent());
            return;
        }
        if (node instanceof Modifier) {
            Modifier modifier = (Modifier) node;
            nodeText.addToken(LexicalDifferenceCalculator.toToken(modifier), modifier.getKeyword().asString());
            return;
        }
        interpret(node, ConcreteSyntaxModel.forClass(node.getClass()), nodeText);
    }

    /**
     * TODO: Process CsmIndent and CsmUnindent before reaching this point
     */
    private static NodeText interpret(Node node, CsmElement csm, NodeText nodeText) {
        LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(csm, node);
        List<TextElement> indentation = findIndentation(node);
        boolean pendingIndentation = false;
        // Add a comment and line separator if necessary
        node.getComment().ifPresent(n -> {
            LineSeparator lineSeparator = n.getLineEndingStyleOrDefault(LineSeparator.SYSTEM);
            calculatedSyntaxModel.elements.add(0,new CsmToken(eolTokenKind(lineSeparator), lineSeparator.asRawString()));
            calculatedSyntaxModel.elements.add(0,new CsmChild(n));
        });
        for (CsmElement element : calculatedSyntaxModel.elements) {
            if (element instanceof CsmIndent) {
                int indexCurrentElement = calculatedSyntaxModel.elements.indexOf(element);
                if (calculatedSyntaxModel.elements.size() > indexCurrentElement && !(calculatedSyntaxModel.elements.get(indexCurrentElement + 1) instanceof CsmUnindent)) {
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
                nodeText.addToken(csmToken.getTokenType(), csmToken.getContent(node));
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
                    throw new UnsupportedOperationException(element.getClass().getSimpleName());
                }
            }
        }
        // Array brackets are a pain... we do not have a way to represent them explicitly in the AST
        // so they have to be handled in a special way
        if (node instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator) node;
            variableDeclarator.getParentNode().ifPresent(parent -> ((NodeWithVariables<?>) parent).getMaximumCommonType().ifPresent(mct -> {
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
            if (m.getParameterCount() == 0 && m.getReturnType().getCanonicalName().equals(JAVAPARSER_AST_NODELIST)) {
                try {
                    Object raw = m.invoke(parent);
                    if (!(raw instanceof NodeList)) {
                        throw new IllegalStateException("Expected NodeList, found " + raw.getClass().getCanonicalName());
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
