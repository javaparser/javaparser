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

import com.github.javaparser.ast.Node;

import java.io.IOException;

import static com.github.javaparser.Problem.PROBLEM_BY_BEGIN_POSITION;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Parse Java source code and creates Abstract Syntax Trees.
 *
 * @author Júlio Vilmar Gesser
 */
public final class JavaParser implements JavaParserSugar {
    private final ParserConfiguration configuration;

    private GeneratedJavaParser astParser = null;

    private static JavaParser internalParser = new JavaParser(new ParserConfiguration().setAttributeComments(false));

    /**
     * Instantiate the parser with default configuration. Note that parsing can also be done with the methods on
     * this class.
     * Creating an instance will reduce setup time between parsing files.
     */
    public JavaParser() {
        this(new ParserConfiguration());
    }

    /**
     * Instantiate the parser. Note that parsing can also be done with the methods on this class.
     * Creating an instance will reduce setup time between parsing files.
     */
    public JavaParser(ParserConfiguration configuration) {
        this.configuration = configuration;
    }

    /**
     * Get the non-configuration for this parser.
     *
     * @return The non-configuration for this parser.
     */
    public ParserConfiguration getParserConfiguration() {
        return this.configuration;
    }

    private GeneratedJavaParser getParserForProvider(Provider provider) {
        if (astParser == null) {
            astParser = new GeneratedJavaParser(provider);
        } else {
            astParser.reset(provider);
        }
        astParser.setTabSize(configuration.getTabSize());
        astParser.setStoreTokens(configuration.isStoreTokens());
        return astParser;
    }

    /**
     * @return the parser that is used internally by JavaParser when it needs to parse a string.
     */
    public static JavaParser getInternalParser() {
        return internalParser;
    }

    /**
     * Changes the parser that is used internally by JavaParser. Should not be needed.
     */
    public static void setInternalParser(JavaParser internalParser) {
        JavaParser.internalParser = internalParser;
    }

    /**
     * Parses source code.
     * It takes the source code from a Provider.
     * The start indicates what can be found in the source code (compilation unit, block, import...)
     *
     * @param start refer to the constants in ParseStart to see what can be parsed.
     * @param provider refer to Providers to see how you can read source. The provider will be closed after parsing.
     * @param <N> the subclass of Node that is the result of parsing in the start.
     * @return the parse result, a collection of encountered problems, and some extra data.
     */
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        assertNotNull(start);
        assertNotNull(provider);
        final GeneratedJavaParser parser = getParserForProvider(provider);
        try {
            N resultNode = start.parse(parser);
            ParseResult<N> result = new ParseResult<>(resultNode, parser.problems, parser.getTokens(),
                    parser.getCommentsCollection());

            configuration.getPostProcessors().forEach(postProcessor ->
                    postProcessor.process(result, configuration));

            result.getProblems().sort(PROBLEM_BY_BEGIN_POSITION);

            return result;
        } catch (Exception e) {
            final String message = e.getMessage() == null ? "Unknown error" : e.getMessage();
            parser.problems.add(new Problem(message, null, e));
            return new ParseResult<>(null, parser.problems, parser.getTokens(), parser.getCommentsCollection());
        } finally {
            try {
                provider.close();
            } catch (IOException e) {
                // Since we're done parsing and have our result, we don't care about any errors.
            }
        }
    }
}
