/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.issues;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3255Test {

    private static final String EOL = LineSeparator.SYSTEM.asRawString();

    @Test
    public void test() {
        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse("class Test {" + EOL +
                "    private void bad() {" + EOL +
                "        String record = \"\";" + EOL +
                "        record.getBytes();" + EOL +
                "    }" + EOL +
                "}");

        assertEquals(0, parseResult.getProblems().size());

        CompilationUnit compilationUnit = parseResult.getResult().get();
    }

    @Test
    public void test2() {
        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse("class Test {" + EOL +
                "    private void bad() {" + EOL +
                "        String record2 = \"\";" + EOL +
                "        record2.getBytes();" + EOL +
                "    }" + EOL +
                "}");

        assertEquals(0, parseResult.getProblems().size());

        CompilationUnit compilationUnit = parseResult.getResult().get();
    }

    @Test
    void recordIsAValidVariableNameWhenParsingAStatement() {
        parseStatement("Object record;");
    }

    @Test
    public void recordIsAValidVariableNameWhenUsedInAClass() {
        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse("class Test {" + EOL +
                "    private void goodInJava16() {" + EOL +
                "        Object record;" + EOL +
                "    }" + EOL +
                "}");

        assertEquals(0, parseResult.getProblems().size());

        CompilationUnit compilationUnit = parseResult.getResult().get();
    }

}
