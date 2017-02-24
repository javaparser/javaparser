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

package com.github.javaparser;

import java.util.Optional;

import com.github.javaparser.utils.Utils;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A problem that was encountered during parsing.
 */
public class Problem {
    private final String message;
    private final Range range;
    private final Throwable cause;

    Problem(String message, Range range, Throwable cause) {
        assertNotNull(message);

        this.message = message;
        this.range = range;
        this.cause = cause;
    }

    @Override
    public String toString() {
        StringBuilder str = new StringBuilder(message);
        if (range != null)
            str.append(" at ").append(range.begin);
        if (cause != null) {
            str.append(Utils.EOL).append("Problem stacktrace : ").append(Utils.EOL);
            for (int i = 0; i < cause.getStackTrace().length; i++) {
                StackTraceElement ste = cause.getStackTrace()[i];
                str.append("  ").append(ste.toString());
                if (i + 1 != cause.getStackTrace().length)
                    str.append(Utils.EOL);
            }
        }
        return str.toString();
    }

    public String getMessage() {
        return message;
    }

    public Optional<Range> getRange() {
        return Optional.ofNullable(range);
    }

    public Optional<Throwable> getCause() {
        return Optional.ofNullable(cause);
    }
}
