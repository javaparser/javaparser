package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;

import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

class RemovedGroup implements Iterable<Removed> {

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
     */
    public static RemovedGroup of(Integer firstElementIndex, List<Removed> removedList) {
        return new RemovedGroup(firstElementIndex, removedList);
    }

    /**
     * Marks the RemovedGroup as processed which indicates that it should not be processed again
     */
    void processed() {
        isProcessed = true;
    }

    /**
     * Returns whether the RemovedGroup was already processed and should not be processed again
     *
     * @return wheter the RemovedGroup was already processed
     */
    boolean isProcessed() {
        return isProcessed;
    }

    private List<Integer> getIndicesBeingRemoved() {
        return IntStream.range(firstElementIndex, firstElementIndex + removedList.size())
                .boxed()
                .collect(Collectors.toList());
    }

    /**
     * Returns the difference index of the last element being removed with this RemovedGroup
     *
     * @return the last difference incex of this RemovedGroup
     */
    Integer getLastElementIndex() {
        List<Integer> indicesBeingRemoved = getIndicesBeingRemoved();
        return indicesBeingRemoved.get(indicesBeingRemoved.size() - 1);
    }

    /**
     * Returns the first element of this RemovedGroup
     *
     * @return the first element of this RemovedGroup
     */
    Removed getFirstElement() {
        return removedList.get(0);
    }

    /**
     * Returns the last element of this RemovedGroup
     *
     * @return the last element of this RemovedGroup
     */
    Removed getLastElement() {
        return removedList.get(removedList.size() - 1);
    }

    /**
     * Returns true if the RemovedGroup equates to a complete line
     * This is the case if there are only spaces and tabs left on the line besides the Removed elements.
     *
     * @return true if the RemovedGroup equates to a complete line
     */
    boolean isACompleteLine() {
        Removed firstElement = getFirstElement();

        boolean hasOnlyWhitespaceInFront = false;
        if (firstElement.isChild()) {
            LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) firstElement.getElement();
            Node child = csmChild.getChild();

            Optional<TokenRange> tokenRange = child.getTokenRange();
            if (tokenRange.isPresent()) {
                JavaToken begin = tokenRange.get().getBegin();

                hasOnlyWhitespaceInFront = hasOnlyWhitespaceInFront(begin);
            }
        } else if (firstElement.isToken()) {
            CsmToken token = (CsmToken) firstElement.getElement();
            if (TokenTypes.isEndOfLineToken(token.getTokenType())) {
                hasOnlyWhitespaceInFront = true;
            }
        }

        Removed lastElement = getLastElement();
        boolean hasOnlyWhitespaceBehind = false;
        if (lastElement.isChild()) {
            LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) lastElement.getElement();
            Node child = csmChild.getChild();

            Optional<TokenRange> tokenRange = child.getTokenRange();
            if (tokenRange.isPresent()) {
                JavaToken end = tokenRange.get().getEnd();

                hasOnlyWhitespaceBehind = hasOnlyWhitespaceBehind(end);
            }
        } else if (lastElement.isToken()) {
            CsmToken token = (CsmToken) lastElement.getElement();
            if (TokenTypes.isEndOfLineToken(token.getTokenType())) {
                hasOnlyWhitespaceBehind = true;
            }
        }

        return hasOnlyWhitespaceInFront && hasOnlyWhitespaceBehind;
    }

    private boolean hasOnlyWhitespaceInFront(JavaToken token) {
        Optional<JavaToken> previousToken = token.getPreviousToken();

        if (previousToken.isPresent()) {
            if (TokenTypes.isSpaceOrTab(previousToken.get().getKind())){
                return hasOnlyWhitespaceInFront(previousToken.get());
            } else if (TokenTypes.isEndOfLineToken(previousToken.get().getKind())) {
                return true;
            } else {
                return false;
            }
        }

        return true;
    }

    private boolean hasOnlyWhitespaceBehind(JavaToken token) {
        Optional<JavaToken> nextToken = token.getNextToken();

        if (nextToken.isPresent()) {
            if (TokenTypes.isSpaceOrTab(nextToken.get().getKind())) {
                return hasOnlyWhitespaceInFront(nextToken.get());
            } else if (TokenTypes.isEndOfLineToken(nextToken.get().getKind())) {
                return true;
            } else {
                return false;
            }
        }

        return true;
    }

    /**
     * Returns the indentation in front of this RemovedGroup if possible.
     * If there is something else than whitespace in front, Optional.empty() is returned.
     *
     * @return the indentation in front of this RemovedGroup or Optional.empty()
     */
    Optional<Integer> getIndentation() {
        Removed firstElement = getFirstElement();

        int indentation = 0;
        if (firstElement.isChild()) {
            LexicalDifferenceCalculator.CsmChild csmChild = (LexicalDifferenceCalculator.CsmChild) firstElement.getElement();
            Node child = csmChild.getChild();

            Optional<TokenRange> tokenRange = child.getTokenRange();
            if (tokenRange.isPresent()) {
                JavaToken begin = tokenRange.get().getBegin();

                if (hasOnlyWhitespaceInFront(begin)) {
                    Optional<JavaToken> previousToken = begin.getPreviousToken();

                    while(previousToken.isPresent() && (TokenTypes.isSpaceOrTab(previousToken.get().getKind()))) {
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
    public Iterator<Removed> iterator() {
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