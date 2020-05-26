/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
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
package com.github.javaparser;

import com.github.javaparser.utils.LineEnding;

import javax.sound.sampled.Line;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * {@link Provider} un-escaping unicode escape sequences in the input sequence.
 */
public class LineEndingProcessingProvider implements Provider {

    private static final char LF = '\n';

    private static final char CR = '\r';

    private static final char BACKSLASH = '\\';

    private static final int EOF = -1;

    private static final int INITIAL_BUFFER_SIZE = 2048;

    private char[] _data;

    private Map<LineEnding, Integer> eolCounts = new HashMap<>();

    /**
     * The number of characters in {@link #_data}.
     */
    private int _len = 0;

    /**
     * The position in {@link #_data} where to read the next source character from.
     */
    private int _pos = 0;

    private Provider _input;

    /**
     * Creates a {@link LineEndingProcessingProvider}.
     */
    public LineEndingProcessingProvider(Provider input) {
        this(INITIAL_BUFFER_SIZE, input);
    }

    /**
     * Creates a {@link LineEndingProcessingProvider}.
     */
    public LineEndingProcessingProvider(int bufferSize, Provider input) {
        _input = input;
        _data = new char[bufferSize];
    }

    public LineEnding getDetectedLineEnding() {
        return LineEnding.getLineEnding(
                eolCounts.getOrDefault(LineEnding.CR, 0),
                eolCounts.getOrDefault(LineEnding.LF, 0),
                eolCounts.getOrDefault(LineEnding.CRLF, 0)
        );
    }

    @Override
    public int read(char[] buffer, final int offset, int len) throws IOException {
        int pos = offset;
        int stop = offset + len;
        while (pos < stop) {
            int ch = nextBufferedChar();
            if (ch < 0) {
                if (pos == offset) {
                    // Nothing read yet, this is the end of the stream.
                    return EOF;
                } else {
                    break;
                }
            } else {
                Optional<LineEnding> lookup = LineEnding.lookup(String.valueOf(ch));
                lookup.ifPresent(lineEnding -> {
                    eolCounts.putIfAbsent(lineEnding, 0);
                    eolCounts.put(lineEnding, eolCounts.get(lineEnding) + 1);
                });

                // Move to next character
                buffer[pos++] = (char) ch;
            }
        }
        return pos - offset;
    }

    @Override
    public void close() throws IOException {
        _input.close();
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

    private boolean isBufferEmpty() {
        return _pos >= _len;
    }

    private int fillBuffer() throws IOException {
        _pos = 0;
        int direct = _input.read(_data, 0, _data.length);
        if (direct != 0) {
            _len = direct;
        }
        return direct;
    }


}
