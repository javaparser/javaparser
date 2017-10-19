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

import java.text.Normalizer;
import java.util.Deque;
import java.util.LinkedList;
import java.util.regex.Pattern;

import com.github.javaparser.Position;
import com.github.javaparser.utils.Utils;

public class SourcePrinter {

    private static final Pattern NEWLINE_PATTERN = Pattern.compile("\r\n|\r|\n");

    private final String indentation;
    private final String endOfLineCharacter;
    private int level = 0;
    private boolean indented = false;
    private final StringBuilder buf = new StringBuilder();
    private Position cursor = new Position(1, 0);
    private Deque<Position> methodChainPositions = new LinkedList<>();

    SourcePrinter(final String indentation, final String endOfLineCharacter) {
        this.indentation = indentation;
        this.endOfLineCharacter = endOfLineCharacter;
        pushMethodChainPosition(cursor); // initialize a default position for methodChainPositions, it is expected by method #resetMethodChainPosition()
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
            bufAppend(indentation);
        }
    }

    public SourcePrinter print(final String arg) {
        if (!indented) {
            makeIndent();
            indented = true;
        }
        bufAppend(arg);
        return this;
    }

    public SourcePrinter println(final String arg) {
        print(arg);
        println();
        return this;
    }

    public SourcePrinter println() {
        bufAppend(endOfLineCharacter);
        indented = false;
        return this;
    }

    private StringBuilder bufAppend(final String arg) {
        updateCursor(arg);
        return buf.append(arg);
    }

    private void updateCursor(String arg) {
        String[] lines = NEWLINE_PATTERN.split(arg);
        if ( lines.length == 0 ) {
            cursor = Position.pos(cursor.line + 1, 0);
        } else if ( lines.length == 1 ) {
            cursor = Position.pos(cursor.line, cursor.column + Normalizer.normalize(lines[0],Normalizer.Form.NFC).length() );
        } else {
            cursor = Position.pos(cursor.line + (lines.length -1), 0 + Normalizer.normalize(lines[lines.length-1],Normalizer.Form.NFC).length());
        }
    }

    public Position getCursor() {
        return cursor;
    }

    public void resetMethodChainPosition(Position position) {
        this.methodChainPositions.pop();
        this.methodChainPositions.push(position);
    }

    public void pushMethodChainPosition(Position position) {
        this.methodChainPositions.push(position);
    }

    public Position peekMethodChainPosition() {
        return this.methodChainPositions.peek();
    }

    public Position popMethodChainPosition() {
        return this.methodChainPositions.pop();
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
