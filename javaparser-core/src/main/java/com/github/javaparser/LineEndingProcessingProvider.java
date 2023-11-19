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
package com.github.javaparser;

import com.github.javaparser.utils.LineSeparator;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * {@link Provider} un-escaping unicode escape sequences in the input sequence.
 */
public class LineEndingProcessingProvider implements Provider {

    private static final int EOF = -1;

    private static final int DEFAULT_BUFFER_SIZE = 2048;

    /**
     * The "other" provider which we are wrapping around / reading from.
     */
    private final Provider _input;

    /**
     * The buffer that we're storing data within.
     */
    private final char[] _data;

    /**
     * The number of characters in {@link #_data}.
     */
    private int _len = 0;

    /**
     * The position in {@link #_data} where to read the next source character from.
     */
    private int _pos = 0;

    private final Map<LineSeparator, Integer> eolCounts = new HashMap<>();

    public LineEndingProcessingProvider(Provider input) {
        this(DEFAULT_BUFFER_SIZE, input);
    }

    public LineEndingProcessingProvider(int bufferSize, Provider input) {
        _input = input;
        _data = new char[bufferSize];
    }

    @Override
    public void close() throws IOException {
        _input.close();
    }

    private int fillBuffer() throws IOException {
        _pos = 0;
        int direct = _input.read(_data, 0, _data.length);
        if (direct != 0) {
            _len = direct;
        }
        return direct;
    }

    public LineSeparator getDetectedLineEnding() {
        return LineSeparator.getLineEnding(eolCounts.getOrDefault(LineSeparator.CR, 0), eolCounts.getOrDefault(LineSeparator.LF, 0), eolCounts.getOrDefault(LineSeparator.CRLF, 0));
    }

    private boolean isBufferEmpty() {
        return _pos >= _len;
    }

    /**
     * Retrieves the next un-escaped character from the buffered {@link #_input}.
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
        return _data[_pos++];
    }

    @Override
    public int read(char[] buffer, final int offset, int len) throws IOException {
        int pos = offset;
        int stop = offset + len;
        LineSeparator previousLineSeparator = null;
        while (pos < stop) {
            int ch = nextBufferedChar();
            if (ch < 0) {
                if (pos == offset) {
                    // Nothing read yet, this is the end of the stream.
                    return EOF;
                }
                break;
            }
            String str = String.valueOf((char) ch);
            Optional<LineSeparator> lookup = LineSeparator.lookup(str);
            if (lookup.isPresent()) {
                LineSeparator lineSeparator = lookup.get();
                // Track the number of times this character is found..
                eolCounts.putIfAbsent(lineSeparator, 0);
                eolCounts.put(lineSeparator, eolCounts.get(lineSeparator) + 1);
                // Handle line separators of length two (specifically CRLF)
                // TODO: Make this more generic than just CRLF (e.g. track the previous char rather than the previous line separator
                if (lineSeparator == LineSeparator.LF) {
                    if (previousLineSeparator == LineSeparator.CR) {
                        eolCounts.putIfAbsent(LineSeparator.CRLF, 0);
                        eolCounts.put(LineSeparator.CRLF, eolCounts.get(LineSeparator.CRLF) + 1);
                    }
                }
                // If "this" (current) char <strong>is</strong> a line separator, set the next loop's "previous" to this
                previousLineSeparator = lineSeparator;
            } else {
                // If "this" (current) char <strong>is not</strong> a line separator, set the next loop's "previous" to null
                previousLineSeparator = null;
            }
            buffer[pos++] = (char) ch;
        }
        return pos - offset;
    }
}
