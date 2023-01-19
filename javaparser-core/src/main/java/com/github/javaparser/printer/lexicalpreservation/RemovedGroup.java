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
import com.github.javaparser.TokenRange;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;

import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * This class represents a group of {@link Removed} elements.
 * The {@link Removed} elements are ideally consecutive for the methods in this class to work correctly.
 *
 * This class consists of methods that calculate information to better handle the difference application for the
 * containing {@link Removed} elements.
 *
 * @see Iterable
 *
 * @author ThLeu
 */
final class RemovedGroup implements Iterable<Removed> {

    private final Integer firstElementIndex;

    private final List<Removed> removedList;

    private boolean isProcessed = false;

    private RemovedGroup(Integer firstElementIndex, List<Removed> removedList) {
        if (firstElementIndex == null) {
            throw new IllegalArgumentException("firstElementIndex should not be null");
        }
        if (removedList == null || removedList.isEmpty()) {
            throw new IllegalArgumentException("removedList should not be null or empty");
        }
        this.firstElementIndex = firstElementIndex;
        this.removedList = removedList;
    }

    /**
     * Factory method to create a RemovedGroup which consists of consecutive Removed elements
     *
     * @param firstElementIndex the difference index at which the RemovedGroup starts
     * @param removedList list of the consecutive Removed elements
     * @return a RemovedGroup object
     * @throws IllegalArgumentException if the firstElementIndex is null or the removedList is empty or null
     */
    public static RemovedGroup of(Integer firstElementIndex, List<Removed> removedList) {
        return new RemovedGroup(firstElementIndex, removedList);
    }

    /**
     * Marks the RemovedGroup as processed which indicates that it should not be processed again
     */
    final void processed() {
        isProcessed = true;
    }

    /**
     * Returns whether the RemovedGroup was already processed and should not be processed again
     *
     * @return wheter the RemovedGroup was already processed
     */
    final boolean isProcessed() {
        return isProcessed;
    }

    private List<Integer> getIndicesBeingRemoved() {
        return IntStream.range(firstElementIndex, firstElementIndex + removedList.size()).boxed().collect(Collectors.toList());
    }

    /**
     * Returns the difference index of the last element being removed with this RemovedGroup
     *
     * @return the last difference incex of this RemovedGroup
     */
    final Integer getLastElementIndex() {
        List<Integer> indicesBeingRemoved = getIndicesBeingRemoved();
        return indicesBeingRemoved.get(indicesBeingRemoved.size() - 1);
    }

    /**
     * Returns the first element of this RemovedGroup
     *
     * @return the first element of this RemovedGroup
     */
    final Removed getFirstElement() {
        return removedList.get(0);
    }

    /**
     * Returns the last element of this RemovedGroup
     *
     * @return the last element of this RemovedGroup
     */
    final Removed getLastElement() {
        return removedList.get(removedList.size() - 1);
    }
    
    /**
     * Returns true if the specified element is the last element of this RemovedGroup
     *
     */
    final boolean isLastElement(Removed element) {
        return getLastElement().equals(element);
    }

    /**
     * Returns true if the RemovedGroup equates to a complete line
     * This is the case if there are only spaces and tabs left on the line besides the Removed elements.
     * <br>
     * Example:
     * <pre>
     * "  [Removed] [EOL]" -> this would be a complete line, regardless of spaces or tabs before or after the [Removed] element
     * "  [Removed] void [EOL]" -> this would not be a complete line because of the "void"
     * "  public [Removed] [EOL]" -> this would not be a complete line because of the "public"
     * </pre>
     *
     * @return true if the RemovedGroup equates to a complete line
     */
    final boolean isACompleteLine() {
        return hasOnlyWhitespace(getFirstElement(), hasOnlyWhitespaceInFrontFunction) && hasOnlyWhitespace(getLastElement(), hasOnlyWhitespaceBehindFunction);
    }

    private final Function<JavaToken, Boolean> hasOnlyWhitespaceJavaTokenInFrontFunction = begin -> hasOnlyWhiteSpaceForTokenFunction(begin, token -> token.getPreviousToken());

    private final Function<JavaToken, Boolean> hasOnlyWhitespaceJavaTokenBehindFunction = end -> hasOnlyWhiteSpaceForTokenFunction(end, token -> token.getNextToken());

    private final Function<TokenRange, Boolean> hasOnlyWhitespaceInFrontFunction = tokenRange -> hasOnlyWhitespaceJavaTokenInFrontFunction.apply(tokenRange.getBegin());

    private final Function<TokenRange, Boolean> hasOnlyWhitespaceBehindFunction = tokenRange -> hasOnlyWhitespaceJavaTokenBehindFunction.apply(tokenRange.getEnd());

    private boolean hasOnlyWhitespace(Removed startElement, Function<TokenRange, Boolean> hasOnlyWhitespaceFunction) {
        boolean hasOnlyWhitespace = false;
        if (startElement.isChild()) {
            LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) startElement.getElement();
            Node child = csmChild.getChild();
            Optional<TokenRange> tokenRange = child.getTokenRange();
            if (tokenRange.isPresent()) {
                hasOnlyWhitespace = hasOnlyWhitespaceFunction.apply(tokenRange.get());
            }
        } else if (startElement.isToken()) {
            CsmToken token = (CsmToken) startElement.getElement();
            if (token.isNewLine()) {
                hasOnlyWhitespace = true;
            }
        }
        return hasOnlyWhitespace;
    }

    private boolean hasOnlyWhiteSpaceForTokenFunction(JavaToken token, Function<JavaToken, Optional<JavaToken>> tokenFunction) {
        Optional<JavaToken> tokenResult = tokenFunction.apply(token);
        if (tokenResult.isPresent()) {
            if (TokenTypes.isWhitespaceButNotEndOfLine(tokenResult.get().getKind())) {
                return hasOnlyWhiteSpaceForTokenFunction(tokenResult.get(), tokenFunction);
            } else if (TokenTypes.isEndOfLineToken(tokenResult.get().getKind())) {
                return true;
            } else {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns the indentation in front of this RemovedGroup if possible.
     * Sometimes the first deleted element may be a line break because the <code>ConcreteSyntaxModel</code> generates a line break before the members (for example FieldDeclaration).
     * In this case a remove operation on the member will generate the deletion of the first line break.
     * It is therefore necessary to avoid taking this element into account so we're looking for the first element that isn't a line break..
     * For example
     * class Foo {
     *     int x;
     * }
     * If there is something else than whitespace in front this element, Optional.empty() is returned.
     *
     * @return the indentation in front of this RemovedGroup or Optional.empty()
     */
    final Optional<Integer> getIndentation() {
        Removed firstElement = null;
        int indentation = 0;
        // search for the first element which is not a new line
        Iterator it = iterator();
        while (it.hasNext()) {
            firstElement = (Removed) it.next();
            if (firstElement.isNewLine())
                continue;
            break;
        }
        if (firstElement.isChild()) {
            LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) firstElement.getElement();
            Node child = csmChild.getChild();
            Optional<TokenRange> tokenRange = child.getTokenRange();
            if (tokenRange.isPresent()) {
                JavaToken begin = tokenRange.get().getBegin();
                if (hasOnlyWhitespaceJavaTokenInFrontFunction.apply(begin)) {
                    Optional<JavaToken> previousToken = begin.getPreviousToken();
                    while (previousToken.isPresent() && (TokenTypes.isWhitespaceButNotEndOfLine(previousToken.get().getKind()))) {
                        indentation++;
                        previousToken = previousToken.get().getPreviousToken();
                    }
                    if (previousToken.isPresent()) {
                        if (TokenTypes.isEndOfLineToken(previousToken.get().getKind())) {
                            return Optional.of(Integer.valueOf(indentation));
                        } else {
                            return Optional.empty();
                        }
                    } else {
                        return Optional.of(Integer.valueOf(indentation));
                    }
                }
            }
        }
        return Optional.empty();
    }

    @Override
    public final Iterator<Removed> iterator() {
        return new Iterator<Removed>() {

            private int currentIndex = 0;

            @Override
            public boolean hasNext() {
                return currentIndex < removedList.size() && removedList.get(currentIndex) != null;
            }

            @Override
            public Removed next() {
                return removedList.get(currentIndex++);
            }
        };
    }
}
