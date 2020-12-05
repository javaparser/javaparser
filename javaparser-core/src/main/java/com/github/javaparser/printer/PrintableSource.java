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

import com.github.javaparser.Position;

public interface PrintableSource {

    /**
     * Add the default indentation to the current indentation and push it on the indentation stack.
     * Does not actually output anything.
     */
    PrintableSource indent();

    /**
     * Add to the current indentation until it is reaches "column" and push it on the indentation stack.
     * Does not actually output anything.
     */
    PrintableSource indentWithAlignTo(int column);

    /**
     * Pop the last indentation of the indentation stack.
     * Does not actually output anything.
     */
    PrintableSource unindent();

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
     * @see PrintableSource#println(String)
     */
    PrintableSource print(String arg);

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
    PrintableSource println(String arg);

    /**
     * Append a newline to the buffer.
     *
     * @return this instance, for nesting calls to method as fluent interface
     */
    PrintableSource println();

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
    Position getCursor();

    /**
     * @return the currently printed source code.
     */
    String toString();

    /**
     * Changes all EOL characters in "content" to the EOL character this SourcePrinter is using.
     */
    String normalizeEolInTextBlock(String content);

    /**
     * Set the top-most indent to the column the cursor is currently in, can be undone with
     * {@link #reindentToPreviousLevel()}. Does not actually output anything.
     */
    void reindentWithAlignToCursor();

    /**
     * Set the top-most indent to the column the cursor was before the last {@link #reindentWithAlignToCursor()} call.
     * Does not actually output anything.
     */
    void reindentToPreviousLevel();

    /**
     * Adds an indent to the top of the stack that is a copy of the current top indent.
     * With this you announce "I'm going to indent the next line(s)" but not how far yet.
     * Once you do know, you can pop this indent ("unindent") and indent to the right column.
     * (Does not actually output anything.)
     */
    void duplicateIndent();

}