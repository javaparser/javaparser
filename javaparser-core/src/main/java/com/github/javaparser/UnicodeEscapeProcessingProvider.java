/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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
package com.github.javaparser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * {@link Provider} un-escaping unicode escape sequences in the input sequence.
 */
public class UnicodeEscapeProcessingProvider implements Provider {

    private static final char LF = '\n';

    private static final char CR = '\r';

    private static final char BACKSLASH = '\\';

    private static final int EOF = -1;

    private char[] data;

    /**
     * The number of characters in {@link #data}.
     */
    private int len = 0;

    /**
     * The position in {@link #data} where to read the next source character from.
     */
    private int pos = 0;

    private boolean backslashSeen;

    private final LineCounter inputLine = new LineCounter();

    private final LineCounter outputLine = new LineCounter();

    private final PositionMappingBuilder mappingBuilder = new PositionMappingBuilder(outputLine, inputLine);

    private final Provider input;

    /**
     * Creates a {@link UnicodeEscapeProcessingProvider}.
     */
    public UnicodeEscapeProcessingProvider(Provider input) {
        this(2048, input);
    }

    /**
     * Creates a {@link UnicodeEscapeProcessingProvider}.
     */
    public UnicodeEscapeProcessingProvider(int bufferSize, Provider input) {
        this.input = input;
        data = new char[bufferSize];
    }

    /**
     * The {@link LineCounter} of the input file.
     */
    public LineCounter getInputCounter() {
        return inputLine;
    }

    /**
     * The {@link LineCounter} of the output file.
     */
    public LineCounter getOutputCounter() {
        return outputLine;
    }

    @Override
    public int read(char[] buffer, final int offset, int len) throws IOException {
        int pos = offset;
        int stop = offset + len;
        while (pos < stop) {
            int ch = outputLine.process(nextOutputChar());
            if (ch < 0) {
                if (pos == offset) {
                    // Nothing read yet, this is the end of the stream.
                    return EOF;
                } else {
                    break;
                }
            } else {
                mappingBuilder.update();
                buffer[pos++] = (char) ch;
            }
        }
        return pos - offset;
    }

    @Override
    public void close() throws IOException {
        input.close();
    }

    /**
     * Produces the next un-escaped character to be written to the output.
     *
     * @return The next character or {@code -1} if no more characters are available.
     */
    private int nextOutputChar() throws IOException {
        int next = nextInputChar();
        switch (next) {
            case EOF:
                return EOF;
            case BACKSLASH:
                if (backslashSeen) {
                    return clearBackSlashSeen(next);
                } else {
                    return backSlashSeen();
                }
            default:
                // An arbitrary character.
                return clearBackSlashSeen(next);
        }
    }

    private int clearBackSlashSeen(int next) {
        backslashSeen = false;
        return next;
    }

    private int backSlashSeen() throws IOException {
        backslashSeen = true;

        int next = nextInputChar();
        switch (next) {
            case EOF:
                // End of file after backslash produces the backslash itself.
                return BACKSLASH;
            case 'u':
                return unicodeStartSeen();
            default:
                pushBack(next);
                return BACKSLASH;
        }
    }

    private int unicodeStartSeen() throws IOException {
        int uCnt = 1;
        while (true) {
            int next = nextInputChar();
            switch (next) {
                case EOF:
                    pushBackUs(uCnt);
                    return BACKSLASH;
                case 'u':
                    uCnt++;
                    continue;
                default:
                    return readDigits(uCnt, next);
            }
        }
    }

    private int readDigits(int uCnt, int next3) throws IOException {
        int digit3 = digit(next3);
        if (digit3 < 0) {
            pushBack(next3);
            pushBackUs(uCnt);
            return BACKSLASH;
        }

        int next2 = nextInputChar();
        int digit2 = digit(next2);
        if (digit2 < 0) {
            pushBack(next2);
            pushBack(next3);
            pushBackUs(uCnt);
            return BACKSLASH;
        }

        int next1 = nextInputChar();
        int digit1 = digit(next1);
        if (digit1 < 0) {
            pushBack(next1);
            pushBack(next2);
            pushBack(next3);
            pushBackUs(uCnt);
            return BACKSLASH;
        }

        int next0 = nextInputChar();
        int digit0 = digit(next0);
        if (digit0 < 0) {
            pushBack(next0);
            pushBack(next1);
            pushBack(next2);
            pushBack(next3);
            pushBackUs(uCnt);
            return BACKSLASH;
        }

        int ch = digit3 << 12 | digit2 << 8 | digit1 << 4 | digit0;
        return clearBackSlashSeen(ch);
    }

    private void pushBackUs(int cnt) {
        for (int n = 0; n < cnt; n++) {
            pushBack('u');
        }
    }

    private static int digit(int ch) {
        if (ch >= '0' && ch <= '9') {
            return ch - '0';
        }
        if (ch >= 'A' && ch <= 'F') {
            return 10 + ch - 'A';
        }
        if (ch >= 'a' && ch <= 'f') {
            return 10 + ch - 'a';
        }
        return -1;
    }

    /**
     * Processes column/line information from the input file.
     *
     * @return The next character or {@code -1} if no more input is available.
     */
    private int nextInputChar() throws IOException {
        int result = nextBufferedChar();
        return inputLine.process(result);
    }

    /**
     * Retrieves the next un-escaped character from the buffered {@link #input}.
     *
     * @return The next character or {@code -1} if no more input is available.
     */
    private int nextBufferedChar() throws IOException {
        while (isBufferEmpty()) {
            int direct = fillBuffer();
            if (direct < 0) {
                return EOF;
            }
        }
        return data[pos++];
    }

    private boolean isBufferEmpty() {
        return pos >= len;
    }

    private int fillBuffer() throws IOException {
        pos = 0;
        int direct = input.read(data, 0, data.length);
        if (direct != 0) {
            len = direct;
        }
        return direct;
    }

    private void pushBack(int ch) {
        if (ch < 0) {
            return;
        }

        if (isBufferEmpty()) {
            pos = data.length;
            len = data.length;
        } else if (pos == 0) {
            if (len == data.length) {
                // Buffer is completely full, no push possible, enlarge buffer.
                char[] newData = new char[data.length + 1024];
                len = newData.length;
                pos = newData.length - data.length;
                System.arraycopy(data, 0, newData, pos, data.length);
                data = newData;
            } else {
                // Move contents to the right.
                int cnt = len - pos;
                pos = data.length - len;
                len = data.length;
                System.arraycopy(data, 0, data, pos, cnt);
            }
        }
        data[--pos] = (char) ch;
    }

    /**
     * The {@link PositionMapping} being built during processing the file.
     */
    public PositionMapping getPositionMapping() {
        return mappingBuilder.getMapping();
    }

    /**
     * An algorithm mapping {@link Position} form two corresponding files.
     */
    public static final class PositionMapping {

        private final List<DeltaInfo> deltas = new ArrayList<>();

        /**
         * Creates a {@link UnicodeEscapeProcessingProvider.PositionMapping}.
         */
        public PositionMapping() {
            super();
        }

        /**
         * Whether this is the identity transformation.
         */
        public boolean isEmpty() {
            return deltas.isEmpty();
        }

        void add(int line, int column, int lineDelta, int columnDelta) {
            deltas.add(new DeltaInfo(line, column, lineDelta, columnDelta));
        }

        /**
         * Looks up the {@link PositionUpdate} for the given Position.
         */
        public PositionUpdate lookup(Position position) {
            int result = Collections.binarySearch(deltas, position);
            if (result >= 0) {
                return deltas.get(result);
            } else {
                int insertIndex = -result - 1;
                if (insertIndex == 0) {
                    // Before the first delta info, identity mapping.
                    return PositionUpdate.NONE;
                } else {
                    // The relevant update is the one with the position smaller
                    // than the requested position.
                    return deltas.get(insertIndex - 1);
                }
            }
        }

        /**
         * Algorithm updating a {@link Position} from one file to a
         * {@link Position} in a corresponding file.
         */
        public static interface PositionUpdate {

            /**
             * The identity position mapping.
             */
            PositionUpdate NONE = new PositionUpdate() {
                @Override
                public int transformLine(int line) {
                    return line;
                }

                @Override
                public int transformColumn(int column) {
                    return column;
                }

                @Override
                public Position transform(Position pos) {
                    return pos;
                }
            };

            /**
             * Maps the given line to an original line.
             */
            int transformLine(int line);

            /**
             * Maps the given column to an original column.
             */
            int transformColumn(int column);

            /**
             * The transformed position.
             */
            default Position transform(Position pos) {
                int line = pos.line;
                int column = pos.column;
                int transformedLine = transformLine(line);
                int transformedColumn = transformColumn(column);
                return new Position(transformedLine, transformedColumn);
            }

        }

        private static final class DeltaInfo extends Position implements PositionUpdate {

            /**
             * The offset to add to the {@link #line} and all following source
             * positions up to the next {@link PositionUpdate}.
             */
            private final int lineDelta;

            /**
             * The offset to add to the {@link #column} and all following
             * source positions up to the next {@link PositionUpdate}.
             */
            private final int columnDelta;

            /**
             * Creates a {@link PositionUpdate}.
             */
            public DeltaInfo(int line, int column, int lineDelta,
                    int columnDelta) {
                super(line, column);
                this.lineDelta = lineDelta;
                this.columnDelta = columnDelta;
            }

            @Override
            public int transformLine(int sourceLine) {
                return sourceLine + lineDelta;
            }

            @Override
            public int transformColumn(int sourceColumn) {
                return sourceColumn + columnDelta;
            }

            @Override
            public String toString() {
                return "(" + line + ", " + column + ": " + lineDelta + ", " + columnDelta + ")";
            }

        }

        /**
         * Transforms the given {@link Position}.
         */
        public Position transform(Position pos) {
            return lookup(pos).transform(pos);
        }

        /**
         * Transforms the given {@link Range}.
         */
        public Range transform(Range range) {
            Position begin = transform(range.begin);
            Position end = transform(range.end);
            if (begin == range.begin && end == range.end) {
                // No change.
                return range;
            }
            return new Range(begin, end);
        }
    }

    private static final class PositionMappingBuilder {

        private final LineCounter left;
        private final LineCounter right;

        private final PositionMapping mapping = new PositionMapping();

        private int lineDelta = 0;
        private int columnDelta = 0;

        /**
         * Creates a {@link PositionMappingBuilder}.
         *
         * @param left The source {@link LineCounter}.
         * @param right The target {@link LineCounter}.
         */
        public PositionMappingBuilder(LineCounter left, LineCounter right) {
            this.left = left;
            this.right = right;
            update();
        }

        /**
         * The built {@link PositionMapping}.
         */
        public PositionMapping getMapping() {
            return mapping;
        }

        public void update() {
            int lineDelta = right.getLine() - left.getLine();
            int columnDelta = right.getColumn() - left.getColumn();

            if (lineDelta != this.lineDelta || columnDelta != this.columnDelta) {
                mapping.add(left.getLine(), left.getColumn(), lineDelta, columnDelta);

                this.lineDelta = lineDelta;
                this.columnDelta = columnDelta;
            }
        }

    }

    /**
     * Processor keeping track of the current line and column in a stream of
     * incoming characters.
     *
     * @see #process(int)
     */
    public static final class LineCounter {

        /**
         * Whether {@link #CR} has been seen on the input as last character.
         */
        private boolean crSeen;

        private int line = 1;

        private int column = 1;

        /**
         * Creates a {@link UnicodeEscapeProcessingProvider.LineCounter}.
         */
        public LineCounter() {
            super();
        }

        /**
         * The line of the currently processed input character.
         */
        public int getLine() {
            return line;
        }

        /**
         * The column of the currently processed input character.
         */
        public int getColumn() {
            return column;
        }

        /**
         * The current position.
         */
        public Position getPosition() {
            return new Position(getLine(), getColumn());
        }

        /**
         * Analyzes the given character for line feed.
         */
        public int process(int ch) {
            switch (ch) {
                case EOF:
                    break;
                case CR:
                    incLine();
                    crSeen = true;
                    break;
                case LF:
                    // CR LF does only count as a single line terminator.
                    if (crSeen) {
                        crSeen = false;
                    } else {
                        incLine();
                    }
                    break;
                default:
                    crSeen = false;
                    column++;
            }
            return ch;
        }

        private void incLine() {
            line++;
            column = 1;
        }

    }

}
