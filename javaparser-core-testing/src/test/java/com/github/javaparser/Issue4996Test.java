/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

import org.junit.jupiter.api.Test;

public class Issue4996Test {

    // Template: case label is on line 4, col 13; first pattern starts at col 18; second at col 28.
    private static final String SWITCH_TEMPLATE = "public class Main {\n"
            + "    void m(Object o) {\n"
            + "        switch (o) {\n"
            + "            %s\n"
            + "            default -> {}\n"
            + "        }\n"
            + "    }\n"
            + "}";

    private static final String UPGRADE_SUFFIX =
            " Pay attention that this feature is supported starting from 'JAVA_22' language level."
                    + " If you need that feature the language level must be configured in the"
                    + " configuration before parsing the source files.";

    private static JavaParser parserFor(ParserConfiguration.LanguageLevel level) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(level));
    }

    private static String switchWith(String caseLabel) {
        return String.format(SWITCH_TEMPLATE, caseLabel);
    }

    @Test
    public void testIssue4996() {
        String code = "public class Main {\n" + "    public static void main(String[] args) {\n"
                + "        Object str = \"string\";\n"
                + "\n"
                + "        switch (str) {\n"
                + "            case String _, Integer _ -> f();\n"
                + "            default -> g();\n"
                + "        }\n"
                + "    }\n"
                + "\n"
                + "    private static void f() {\n"
                + "        System.out.println(\"f\");\n"
                + "    }\n"
                + "\n"
                + "    private static void g() {\n"
                + "        System.out.println(\"g\");\n"
                + "    }\n"
                + "}";

        ParserConfiguration config =
                new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_22);
        JavaParser parser = new JavaParser(config);
        assertNoProblems(parser.parse(code));
    }

    @Test
    public void multiPatternWithThreePatternsAcceptedInJava22() {
        assertNoProblems(parserFor(ParserConfiguration.LanguageLevel.JAVA_22)
                .parse(switchWith("case String _, Integer _, Long _ -> {}")));
    }

    @Test
    public void multiPatternRejectedInJava21() {
        // _ is a reserved keyword in Java 21, so named variables are used here.
        assertProblems(
                parserFor(ParserConfiguration.LanguageLevel.JAVA_21)
                        .parse(switchWith("case String s, Integer i -> {}")),
                "(line 4,col 13) Multiple patterns in case labels not supported." + UPGRADE_SUFFIX);
    }

    @Test
    public void multiPatternWithNamedVarRejectedInJava22() {
        // JLS §14.11.1: patterns in a multi-pattern case may not declare named variables.
        // Error is reported at the position of the offending pattern.
        assertProblems(
                parserFor(ParserConfiguration.LanguageLevel.JAVA_22)
                        .parse(switchWith("case String s, Integer _ -> {}")),
                "(line 4,col 18) Multiple patterns in case labels may not declare any pattern variables.");
    }

    @Test
    public void multiPatternBothNamedVarsRejectedInJava22() {
        assertProblems(
                parserFor(ParserConfiguration.LanguageLevel.JAVA_22)
                        .parse(switchWith("case String s, Integer i -> {}")),
                "(line 4,col 18) Multiple patterns in case labels may not declare any pattern variables.",
                "(line 4,col 28) Multiple patterns in case labels may not declare any pattern variables.");
    }
}
