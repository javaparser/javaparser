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

import java.util.List;

import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.Collections.singletonList;

/**
 * Thrown when parsing problems occur during parsing with the static methods on JavaParser.
 */
public class ParseProblemException extends RuntimeException {
    /**
     * The problems that were encountered during parsing
     */
    private final List<Problem> problems;
    private final ParseResult<?> result;

    public ParseProblemException(ParseResult<?> result) {
        super(createMessage(assertNotNull(result.getProblems())));
        this.problems = result.getProblems();
        this.result = result;
    }

    public ParseProblemException(Throwable throwable) {
        this(new ParseResult<>(null, singletonList(new Problem(throwable.getMessage(), null, throwable)), null, null));
    }

    private static String createMessage(List<Problem> problems) {
        StringBuilder message = new StringBuilder();
        for (Problem problem : problems) {
            message.append(problem.toString()).append(EOL);
        }
        return message.toString();
    }

    public List<Problem> getProblems() {
        return problems;
    }

    public ParseResult<?> getResult() {
        return result;
    }
}
