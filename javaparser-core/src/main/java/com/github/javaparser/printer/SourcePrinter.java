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

import com.github.javaparser.Position;
import com.github.javaparser.printer.PrettyPrinterConfiguration.IndentType;
import com.github.javaparser.utils.Utils;

import java.util.Deque;
import java.util.LinkedList;

import static com.github.javaparser.Position.*;

/**
 * A support class for code that outputs formatted source code.
 */
public class SourcePrinter {
    private final String endOfLineCharacter;
    private final String indentation;
    private final int tabWidth;
    private final IndentType indentType;

    private final Deque<String> indents = new LinkedList<>();
    private final Deque<String> reindentedIndents = new LinkedList<>();
    private String lastPrintedIndent = "";
    private final StringBuilder buf = new StringBuilder();
    private Position cursor = new Position(1, 0);
    private boolean indented = false;

    SourcePrinter() {
        this(new PrettyPrinterConfiguration());
    }

    SourcePrinter(final PrettyPrinterConfiguration configuration) {
        indentation = configuration.getIndent();
        endOfLineCharacter = configuration.getEndOfLineCharacter();
        tabWidth = configuration.getTabWidth();
        indentType = configuration.getIndentType();
        indents.push("");
    }

    /**
     * Add the default indentation to the current indentation and push it on the indentation stack.
     * Does not actually output anything.
     */
    public SourcePrinter indent() {
        String currentIndent = indents.peek();
        switch (indentType) {
            case SPACES:
            case TABS_WITH_SPACE_ALIGN:
                indents.push(currentIndent + indentation);
                break;

            case TABS:
                indents.push(indentation + currentIndent);
                break;

            default:
                throw new AssertionError("Unhandled indent type");
        }
        return this;
    }

    /**
     * Add to the current indentation until it is reaches "column" and push it on the indentation stack.
     * Does not actually output anything.
     */
    public SourcePrinter indentWithAlignTo(int column) {
        indents.push(calculateIndentWithAlignTo(column));
        return this;
    }

    private String calculateIndentWithAlignTo(int column) {
        if (column < lastPrintedIndent.length()){
            throw new IllegalStateException("Attempt to indent less than the previous indent.");
        }

        StringBuilder newIndent = new StringBuilder(lastPrintedIndent);
        switch (indentType) {
            case SPACES:
            case TABS_WITH_SPACE_ALIGN:
                while (newIndent.length() < column) {
                    newIndent.append(' ');
                }
                break;

            case TABS:
                int logicalIndentLength = newIndent.length();
                while ((logicalIndentLength + tabWidth) <= column) {
                    newIndent.insert(0, '\t');
                    logicalIndentLength += tabWidth;
                }
                while (logicalIndentLength < column) {
                    newIndent.append(' ');
                    logicalIndentLength++;
                }
                StringBuilder fullTab = new StringBuilder();
                for(int i=0; i<tabWidth; i++){
                    fullTab.append(' ');
                }
                String fullTabString = fullTab.toString();
                if ((newIndent.length() >= tabWidth)
                        && newIndent.substring(newIndent.length() - tabWidth).equals(fullTabString)) {
                    int i = newIndent.indexOf(fullTabString);
                    newIndent.replace(i, i + tabWidth, "\t");
                }
                break;

            default:
                throw new AssertionError("Unhandled indent type");
        }

        return newIndent.toString();
    }

    /**
     * Pop the last indentation of the indentation stack.
     * Does not actually output anything.
     */
    public SourcePrinter unindent() {
        if (indents.isEmpty()) {
            // Since we start out with an empty indent on the stack, this will only occur
            // the second time we over-unindent.
            throw new IllegalStateException("Indent/unindent calls are not well-balanced.");
        }
        indents.pop();
        return this;
    }

    private void append(String arg) {
        buf.append(arg);
        cursor = cursor.withColumn(cursor.column + arg.length());
    }

    /**
     * Append the source string passed as argument to the buffer.
     * If this is being appended at the beginning of a line, performs indentation first.
     * <p>
     * The source line to be printed should not contain newline/carriage-return characters;
     * use {@link #println(String)} to automatically append a newline at the end of the source string.
     * If the source line passed as argument contains newline/carriage-return characters would
     * impredictably affect a correct computation of the current {@link #getCursor()} position.
     *
     * @param arg source line to be printed (should not contain newline/carriage-return characters)
     * @return this instance, for nesting calls to method as fluent interface
     * @see SourcePrinter#println(String)
     */
    public SourcePrinter print(final String arg) {
        if (!indented) {
            lastPrintedIndent = indents.peek();
            append(lastPrintedIndent);
            indented = true;
        }
        append(arg);
        return this;
    }

    /**
     * Append the source string passed as argument to the buffer, then append a newline.
     * If this is being appended at the beginning of a line, performs indentation first.
     * <p>
     * The source line to be printed should not contain newline/carriage-return characters.
     * If the source line passed as argument contains newline/carriage-return characters would
     * impredictably affect a correct computation of the current {@link #getCursor()} position.
     *
     * @param arg source line to be printed (should not contain newline/carriage-return characters)
     * @return this instance, for nesting calls to method as fluent interface
     */
    public SourcePrinter println(final String arg) {
        print(arg);
        println();
        return this;
    }

    /**
     * Append a newline to the buffer.
     *
     * @return this instance, for nesting calls to method as fluent interface
     */
    public SourcePrinter println() {
        buf.append(endOfLineCharacter);
        cursor = pos(cursor.line + 1, 0);
        indented = false;
        return this;
    }

    /**
     * Return the current cursor position (line, column) in the source printer buffer.
     * <p>
     * Please notice in order to guarantee a correct computation of the cursor position,
     * this printer expect the contracts of the methods {@link #print(String)} and {@link #println(String)}
     * has been respected through all method calls, meaning the source string passed as argument to those method
     * calls did not contain newline/carriage-return characters.
     *
     * @return the current cursor position (line, column).
     */
    public Position getCursor() {
        return cursor;
    }

    /**
     * @return the currently printed source code.
     * @deprecated use toString()
     */
    @Deprecated
    public String getSource() {
        return toString();
    }

    /**
     * @return the currently printed source code.
     */
    @Override
    public String toString() {
        return buf.toString();
    }

    /**
     * Changes all EOL characters in "content" to the EOL character this SourcePrinter is using.
     */
    public String normalizeEolInTextBlock(String content) {
        return Utils.normalizeEolInTextBlock(content, endOfLineCharacter);
    }

    /**
     * Set the top-most indent to the column the cursor is currently in, can be undone with
     * {@link #reindentToPreviousLevel()}. Does not actually output anything.
     */
    public void reindentWithAlignToCursor() {
        String newIndent = calculateIndentWithAlignTo(cursor.column);
        reindentedIndents.push(indents.pop());
        indents.push(newIndent);
    }

    /**
     * Set the top-most indent to the column the cursor was before the last {@link #reindentWithAlignToCursor()} call.
     * Does not actually output anything.
     */
    public void reindentToPreviousLevel() {
        if (reindentedIndents.isEmpty()) {
            throw new IllegalStateException("Reindent calls are not well-balanced.");
        }
        indents.pop();
        indents.push(reindentedIndents.pop());
    }

    /**
     * Adds an indent to the top of the stack that is a copy of the current top indent.
     * With this you announce "I'm going to indent the next line(s)" but not how far yet.
     * Once you do know, you can pop this indent ("unindent") and indent to the right column.
     * (Does not actually output anything.)
     */
    public void duplicateIndent() {
        indents.push(indents.peek());
    }
}
