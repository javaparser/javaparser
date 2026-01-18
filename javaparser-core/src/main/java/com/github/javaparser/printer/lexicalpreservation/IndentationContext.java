/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import com.github.javaparser.GeneratedJavaParserConstants;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static com.github.javaparser.printer.lexicalpreservation.IndentationConstants.STANDARD_INDENTATION_SIZE;

/**
 * Maintains the current indentation state during lexical preservation operations.
 *
 * This class encapsulates a mutable list of indentation elements (spaces/tabs)
 * that represents the current indentation level. It provides methods to
 * increase/decrease indentation and query the current state.
 *
 * Instances of this class are typically created at the start of a difference
 * application and maintained throughout the process.
 */
public class IndentationContext {

    /**
     * Current indentation represented as a mutable list of TextElements.
     * Typically contains space or tab tokens.
     */
    private final List<TextElement> elements;

    /**
     * Creates a new IndentationContext with empty indentation.
     */
    public IndentationContext() {
        this.elements = new ArrayList<>();
    }

    /**
     * Creates a new IndentationContext with the specified initial indentation.
     * The provided list is copied to prevent external modifications.
     *
     * @param initialIndentation the initial indentation elements (will be copied)
     */
    public IndentationContext(List<TextElement> initialIndentation) {
        this.elements = new ArrayList<>(initialIndentation);
    }

    /**
     * Increases indentation by one level.
     * Adds STANDARD_INDENTATION_SIZE space characters to the current indentation.
     */
    public void increase() {
        for (int i = 0; i < STANDARD_INDENTATION_SIZE; i++) {
            elements.add(new TokenTextElement(GeneratedJavaParserConstants.SPACE, " "));
        }
    }

    /**
     * Decreases indentation by one level.
     * Removes up to STANDARD_INDENTATION_SIZE characters from the end of the current indentation.
     * Does nothing if the current indentation has fewer elements than STANDARD_INDENTATION_SIZE.
     */
    public void decrease() {
        for (int i = 0; i < STANDARD_INDENTATION_SIZE && !elements.isEmpty(); i++) {
            elements.remove(elements.size() - 1);
        }
    }

    /**
     * Returns a copy of the current indentation elements.
     * The returned list is unmodifiable to prevent accidental modifications.
     *
     * @return unmodifiable view of current indentation elements
     */
    public List<TextElement> getCurrent() {
        return Collections.unmodifiableList(new ArrayList<>(elements));
    }

    /**
     * Returns the number of indentation characters currently stored.
     *
     * @return count of indentation elements
     */
    public int size() {
        return elements.size();
    }

    /**
     * Clears all indentation, resetting to zero indentation.
     */
    public void clear() {
        elements.clear();
    }

    /**
     * Replaces the current indentation with the specified elements.
     * The provided list is copied to prevent external modifications.
     *
     * @param newIndentation the new indentation elements (will be copied)
     */
    public void set(List<TextElement> newIndentation) {
        elements.clear();
        elements.addAll(newIndentation);
    }

    @Override
    public String toString() {
        return "IndentationContext{size=" + elements.size() + ", elements=" + elements + "}";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        IndentationContext that = (IndentationContext) o;
        return elements.equals(that.elements);
    }

    @Override
    public int hashCode() {
        return elements.hashCode();
    }
}