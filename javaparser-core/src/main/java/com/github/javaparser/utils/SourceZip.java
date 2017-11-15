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

package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A collection of Java source files and its sub-directories located in a ZIP or JAR file on the file system.
 * Files can be parsed with a callback.
 *
 */
public class SourceZip {

    private final Path zipPath;
    private ParserConfiguration parserConfiguration;

    /**
     * Create a new ZIP parser. An instance of {@link JavaParser} with the default {@link ParserConfiguration} will be
     * used to parse the ZIP.
     *
     * @param zipPath The absolute path of ZIP file to parse.
     */
    public SourceZip(Path zipPath) {
        this(zipPath, new ParserConfiguration());
    }

    /**
     * Create a new ZIP parser. An instance of {@link JavaParser} with the given configuration will be used to parse
     * the ZIP.
     *
     * @param zipPath The absolute path of ZIP file to parse.
     * @param configuration The configuration to initiate the default parser with.
     */
    public SourceZip(Path zipPath, ParserConfiguration configuration) {
        assertNotNull(zipPath);
        assertNotNull(configuration);
        this.zipPath = zipPath.normalize();
        this.parserConfiguration = configuration;
        Log.info("New source zip at \"%s\"", this.zipPath);
    }

    /**
     * Tries to parse all '.java' files in the ZIP located at this <i>SourceZip</i>'s path and returns the parse
     * results in a list.
     *
     * @return A list of path-compilation unit pairs.
     *
     * @throws IOException If an error occurs while trying to parse the given source.
     */
    public List<Pair<Path, ParseResult<CompilationUnit>>> parse() throws IOException {
        Log.info("Parsing zip at \"%s\"", zipPath);
        List<Pair<Path, ParseResult<CompilationUnit>>> results = new ArrayList<>();
        parse((path, result) -> results.add(new Pair<>(path, result)));
        return results;
    }

    /**
     * Tries to parse all '.java' files in the ZIP located at this <i>SourceZip</i>'s path and returns the parse
     * results in a list.
     *
     * @return A list of path-compilation unit pairs.
     *
     * @throws IOException If an error occurs while trying to parse the given source.
     */
    public SourceZip parse(Callback callback) throws IOException {
        Log.info("Parsing zip at \"%s\"", zipPath);
        JavaParser javaParser = new JavaParser(parserConfiguration);
        try (ZipFile zipFile = new ZipFile(zipPath.toFile())) {
            for (ZipEntry entry : Collections.list(zipFile.entries())) {
                if (!entry.isDirectory() && entry.getName().endsWith(".java")) {
                    Log.info("Parsing zip entry \"%s\"", entry.getName());
                    final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT,
                            provider(zipFile.getInputStream(entry)));
                    callback.process(Paths.get(entry.getName()), result);
                }
            }
        }
        return this;
    }

    /**
     * An interface to define a callback for each file that's parsed.
     */
    @FunctionalInterface
    public interface Callback {

        /**
         * Process the given parse result.
         *
         * @param relativeZipEntryPath The relative path of the entry in the ZIP file that was parsed.
         * @param result The parse result of file located at <i>absolutePath</i>.
         */
        void process(Path relativeZipEntryPath, ParseResult<CompilationUnit> result);
    }

    /**
     * Get the path of the ZIP file to be parsed.
     *
     * @return The absolute path of this ZIP file.
     */
    public Path getZipPath() {
        return zipPath;
    }
    
    /**
     * @deprecated store ParserConfiguration now
     */
    @Deprecated
    public JavaParser getJavaParser() {
        return new JavaParser(parserConfiguration);
    }

    /**
     * Set the parser that is used for parsing by default.
     *
     * @deprecated store ParserConfiguration now
     */
    @Deprecated
    public SourceZip setJavaParser(JavaParser javaParser) {
        assertNotNull(javaParser);
        this.parserConfiguration = javaParser.getParserConfiguration();
        return this;
    }

    public ParserConfiguration getParserConfiguration() {
        return parserConfiguration;
    }

    public SourceZip setParserConfiguration(ParserConfiguration parserConfiguration) {
        assertNotNull(parserConfiguration);
        this.parserConfiguration = parserConfiguration;
        return this;
    }
}
