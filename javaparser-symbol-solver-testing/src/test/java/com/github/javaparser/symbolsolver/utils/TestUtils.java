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

package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;

/**
 * TODO: find a way to reuse the javaparser-core-testing utilities
 */
public class TestUtils {

    /**
     * parse a file using a given parser relative to the classpath root
     */
    public static CompilationUnit parseFile(JavaParser parser, String filePath) {
        try (InputStream in = TestUtils.class.getResourceAsStream(filePath)) {
            ParseResult<CompilationUnit> parse = parser.parse(in);
            List<Problem> problems = parse.getProblems();
            if (!problems.isEmpty()) {
                throw new IllegalStateException(problems.toString());
            }
            return parse.getResult()
                    .orElseThrow(() -> new IllegalArgumentException("No result when attempting to parse " + filePath));
        } catch (IOException ex) {
            throw new IllegalStateException("Error while parsing " + filePath, ex);
        }
    }

    /**
     * parse a file relative to the classpath root
     */
    public static CompilationUnit parseFile(String filePath) {
        return parseFile(new JavaParser(), filePath);
    }

}
