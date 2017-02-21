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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.CommentsCollection;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Path;

import static com.github.javaparser.Providers.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Parse Java's module info format and creates Abstract Syntax Trees.
 *
 * @author Júlio Vilmar Gesser
 */
public final class ModuleInfoParser {
    private final CommentsInserter commentsInserter;
    private final ParserConfiguration configuration;

    private GeneratedModuleInfoParser moduleInfoParser = null;

    /**
     * Instantiate the parser with default configuration. Note that parsing can also be done with the static methods on
     * this class.
     * Creating an instance will reduce setup time between parsing files.
     */
    public ModuleInfoParser() {
        this(new ParserConfiguration());
    }

    /**
     * Instantiate the parser. Note that parsing can also be done with the static methods on this class.
     * Creating an instance will reduce setup time between parsing files.
     */
    public ModuleInfoParser(ParserConfiguration configuration) {
        this.configuration = configuration;
        commentsInserter = new CommentsInserter(configuration);
    }

    private GeneratedModuleInfoParser getParserForProvider(Provider provider) {
        if (moduleInfoParser == null) {
            moduleInfoParser = new GeneratedModuleInfoParser(provider);
        } else {
            moduleInfoParser.reset(provider);
        }
        moduleInfoParser.setTabSize(configuration.getTabSize());
        return moduleInfoParser;
    }

    /**
     * Parses source code.
     * It takes the source code from a Provider.
     * The start indicates what can be found in the source code (compilation unit, block, import...)
     *
     * @param provider refer to Providers to see how you can read source.
     * @return the parse result, a collection of encountered problems, and some extra data.
     */
    public ParseResult<CompilationUnit> parse(Provider provider) {
        assertNotNull(provider);
        try {
            final GeneratedModuleInfoParser parser = getParserForProvider(provider);
            CompilationUnit resultNode = parser.CompilationUnit();
            if (configuration.isAttributeComments()) {
                final CommentsCollection comments = parser.getCommentsCollection();
                commentsInserter.insertComments(resultNode, comments.copy().getComments());
            }

            return new ParseResult<>(resultNode, parser.problems, moduleInfoParser.getTokens(),
                    moduleInfoParser.getCommentsCollection());
        } catch (Exception e) {
            return new ParseResult<>(e);
        } finally {
            try {
                provider.close();
            } catch (IOException e) {
                // Since we're done parsing and have our result, we don't care about any errors.
            }
        }
    }

    /**
     * Parses the module info contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param in {@link InputStream} containing Java source code
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final InputStream in, Charset encoding) {
        return simplifiedParse(provider(in, encoding));
    }

    /**
     * Parses the module info contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param in {@link InputStream} containing Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final InputStream in) {
        return parse(in, UTF8);
    }

    /**
     * Parses the module info contained in a {@link File} and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param file {@link File} containing Java source code
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws FileNotFoundException the file was not found
     */
    public static CompilationUnit parse(final File file, final Charset encoding) throws FileNotFoundException {
        return simplifiedParse(provider(file, encoding));
    }

    /**
     * Parses the module info contained in a {@link File} and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param file {@link File} containing Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws FileNotFoundException the file was not found
     */
    public static CompilationUnit parse(final File file) throws FileNotFoundException {
        return simplifiedParse(provider(file));
    }

    /**
     * Parses the module info contained in a file and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param path path to a file containing Java source code
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws IOException the path could not be accessed
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final Path path, final Charset encoding) throws IOException {
        return simplifiedParse(provider(path, encoding));
    }

    /**
     * Parses the module info contained in a file and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param path path to a file containing Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parse(final Path path) throws IOException {
        return simplifiedParse(provider(path));
    }

    /**
     * Parses the module info contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(final String path) throws IOException {
        return simplifiedParse(resourceProvider(path));
    }

    /**
     * Parses the module info contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(final String path, Charset encoding) throws IOException {
        return simplifiedParse(resourceProvider(path, encoding));
    }

    /**
     * Parses the module info contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param classLoader the classLoader that is asked to load the resource
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(final ClassLoader classLoader, final String path, Charset encoding) throws IOException {
        return simplifiedParse(resourceProvider(classLoader, path, encoding));
    }

    /**
     * Parses module info from a Reader and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param reader the reader containing Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final Reader reader) {
        return simplifiedParse(provider(reader));
    }

    /**
     * Parses the module info contained in code and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param code Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(String code) {
        return simplifiedParse(provider(code));
    }

    private static CompilationUnit simplifiedParse(Provider provider) {
        ParseResult<CompilationUnit> result = new ModuleInfoParser(new ParserConfiguration()).parse(provider);
        return result.getResult().orElseThrow(() -> new ParseProblemException(result.getProblems()));
    }
}
