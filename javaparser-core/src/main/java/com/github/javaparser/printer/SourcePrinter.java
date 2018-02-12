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
import com.github.javaparser.utils.Utils;

public class SourcePrinter {

    private final String indentation;
    private final int indentationLength;
    private final String endOfLineCharacter;
    private int level = 0;
    private boolean indented = false;
    private final StringBuilder buf = new StringBuilder();
    private Position cursor = new Position(1, 0);

    SourcePrinter(final String indentation, final String endOfLineCharacter) {
        this.indentation = indentation;
        this.indentationLength = indentation.length();
        this.endOfLineCharacter = endOfLineCharacter;
    }

    public SourcePrinter indent() {
        level++;
        return this;
    }

    public SourcePrinter unindent() {
        level--;
        return this;
    }

    private void makeIndent() {
        for (int i = 0; i < level; i++) {
            buf.append(indentation);
            cursor = Position.pos(cursor.line, cursor.column + indentationLength);
        }
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
     * @see SourcePrinter#println(String) 
     * @param arg source line to be printed (should not contain newline/carriage-return characters)
     * @return this instance, for nesting calls to method as fluent interface
     */
    public SourcePrinter print(final String arg) {
        if (!indented) {
            makeIndent();
            indented = true;
        }
        buf.append(arg);
        cursor = Position.pos(cursor.line, cursor.column + arg.length());
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
        cursor = Position.pos(cursor.line + 1, 0);
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
     * Performs a new line and indent, then prints enough space characters until aligned to the specified column.
     * @param column the column to align to
     */
    public void wrapToColumn(int column) {
        println();
        if (!indented) {
            makeIndent();
            indented = true;
        }
        while ( cursor.column < column ) {
            print(" ");
        }
    }

    public String getSource() {
        return buf.toString();
    }

    @Override
    public String toString() {
        return getSource();
    }

    public String normalizeEolInTextBlock(String content) {
        return Utils.normalizeEolInTextBlock(content, endOfLineCharacter);
    }
}
