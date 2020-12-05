/*
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

import static com.github.javaparser.printer.configuration.Indentation.IndentType.SPACES;

import java.util.Deque;
import java.util.LinkedList;

import com.github.javaparser.Position;
import com.github.javaparser.printer.configuration.ConfigurablePrinter;
import com.github.javaparser.printer.configuration.Indentation;
import com.github.javaparser.printer.configuration.Indentation.IndentType;
import com.github.javaparser.printer.configuration.PrinterConfiguration.ConfigOption;
import com.github.javaparser.utils.Utils;

/**
 * A support class for code that outputs formatted source code.
 */
public class DefaultPrintableSource implements PrintableSource {
    private final String endOfLineCharacter;
    private final Indentation indentation;

    private final Deque<String> indents = new LinkedList<>();
    private final Deque<String> reindentedIndents = new LinkedList<>();
    private String lastPrintedIndent = "";
    private StringBuilder buf = new StringBuilder();
    private Position cursor = new Position(Position.FIRST_LINE, Position.FIRST_COLUMN - 1); // Start before the first column
    private boolean indented = false;

    public DefaultPrintableSource(final ConfigurablePrinter configuration) {
        indentation = configuration.getIndentation();
        endOfLineCharacter = configuration.get(ConfigOption.END_OF_LINE_CHARACTER).get().asString();
        indents.push("");
    }

    /**
     * Add the default indentation to the current indentation and push it on the indentation stack.
     * Does not actually output anything.
     */
    @Override
    public PrintableSource indent() {
        String currentIndent = indents.peek();
        switch (indentation.getType()) {
            case SPACES:
            case TABS_WITH_SPACE_ALIGN:
                indents.push(currentIndent + indentation.getIndent());
                break;

            case TABS:
                indents.push(indentation.getIndent() + currentIndent);
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
    @Override
    public PrintableSource indentWithAlignTo(int column) {
        indents.push(calculateIndentWithAlignTo(column));
        return this;
    }

    private String calculateIndentWithAlignTo(int column) {
        if (column < lastPrintedIndent.length()){
            throw new IllegalStateException("Attempt to indent less than the previous indent.");
        }

        StringBuilder newIndent = new StringBuilder(lastPrintedIndent);
        switch (indentation.getType()) {
            case SPACES:
            case TABS_WITH_SPACE_ALIGN:
                while (newIndent.length() < column) {
                    newIndent.append(SPACES.getCar());
                }
                break;

            case TABS:
                IndentType currentIndentType = indentation.getType(); 
                int logicalIndentLength = newIndent.length();
                while ((logicalIndentLength + currentIndentType.getWidth()) <= column) {
                    newIndent.insert(0, currentIndentType.getCar());
                    logicalIndentLength += currentIndentType.getWidth();
                }
                while (logicalIndentLength < column) {
                    newIndent.append(SPACES.getCar());
                    logicalIndentLength++;
                }
                StringBuilder fullTab = new StringBuilder();
                for(int i=0; i<currentIndentType.getWidth(); i++){
                    fullTab.append(SPACES.getCar());
                }
                String fullTabString = fullTab.toString();
                if ((newIndent.length() >= currentIndentType.getWidth())
                        && newIndent.substring(newIndent.length() - currentIndentType.getWidth()).equals(fullTabString)) {
                    int i = newIndent.indexOf(fullTabString);
                    newIndent.replace(i, i + currentIndentType.getWidth(), currentIndentType.getCar().toString());
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
    @Override
    public PrintableSource unindent() {
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
     * @see DefaultPrintableSource#println(String)
     */
    @Override
    public PrintableSource print(final String arg) {
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
    @Override
    public PrintableSource println(final String arg) {
        print(arg);
        println();
        return this;
    }

    /**
     * Append a newline to the buffer.
     *
     * @return this instance, for nesting calls to method as fluent interface
     */
    @Override
    public PrintableSource println() {
        buf.append(endOfLineCharacter);
        cursor = new Position(cursor.line + 1, Position.FIRST_COLUMN - 1); // Start before the first column
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
    @Override
    public Position getCursor() {
        return cursor;
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
    @Override
    public String normalizeEolInTextBlock(String content) {
        return Utils.normalizeEolInTextBlock(content, endOfLineCharacter);
    }

    /**
     * Set the top-most indent to the column the cursor is currently in, can be undone with
     * {@link #reindentToPreviousLevel()}. Does not actually output anything.
     */
    @Override
    public void reindentWithAlignToCursor() {
        String newIndent = calculateIndentWithAlignTo(cursor.column);
        reindentedIndents.push(indents.pop());
        indents.push(newIndent);
    }

    /**
     * Set the top-most indent to the column the cursor was before the last {@link #reindentWithAlignToCursor()} call.
     * Does not actually output anything.
     */
    @Override
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
    @Override
    public void duplicateIndent() {
        indents.push(indents.peek());
    }
}
