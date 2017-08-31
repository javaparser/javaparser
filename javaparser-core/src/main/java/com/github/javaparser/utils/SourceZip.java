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

import static com.github.javaparser.utils.Utils.assertNotNull;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;

/**
 * A collection of Java source files and its sub-directories located in a ZIP or JAR file on the file system.
 * Files can be parsed with a callback.
 */
public class SourceZip {

    private final Path zipPath;
    private JavaParser javaParser;

    /**
     * Create a new ZIP parser. A default instance of {@link JavaParser} will be used to parse the ZIP.
     *
     * @param zipPath The absolute path of ZIP file to parse.
     */
    public SourceZip(Path zipPath) {
        assertNotNull(zipPath);
        if (Files.isDirectory(zipPath)
                || !(zipPath.toString().endsWith(".zip") || zipPath.toString().endsWith(".jar"))) {
            throw new IllegalArgumentException("SourceZip only parses ZIP and JAR files.");
        }
        this.zipPath = zipPath.normalize();
        this.javaParser = new JavaParser();
        Log.info("New source zip at \"%s\"", this.zipPath);
    }

    /**
     * Create a new ZIP parser.
     *
     * @param zipPath The absolute path of ZIP file to parse.
     * @param javaParser The parser used to parse the ZIP files.
     */
    public SourceZip(Path zipPath, JavaParser javaParser) {
        this(zipPath);
        assertNotNull(javaParser);
        this.javaParser = javaParser;
    }

    /**
     * Tries to parse all '.java' files in the ZIP located at this <i>SourceZip</i>'s path and passes them one by one
     * to the provided callback.
     *
     * @param callback A callback method for the post-processing of a parsed ZIP file.
     * @return This {@link SourceZip} object.
     */
    public SourceZip parse(Callback callback) throws IOException {
        assertNotNull(callback);
        Log.info("Parsing zip at \"%s\"", zipPath);
        ZipFile zipFile = new ZipFile(zipPath.toFile());
        for (ZipEntry entry : Collections.list(zipFile.entries())) {
            if (!entry.isDirectory() && entry.getName().endsWith(".java")) {
                final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT,
                        provider(zipFile.getInputStream(entry)));
                callback.process(Paths.get(entry.getName()), result);
            }
        }
        zipFile.close();
        return this;
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
     * Get the parser used for parsing.
     *
     * @return The currently set parser.
     */
    public JavaParser getJavaParser() {
        return javaParser;
    }

    /**
     * Set the parser that is used for parsing.
     *
     * @param javaParser The parser to use.
     */
    public SourceZip setJavaParser(JavaParser javaParser) {
        assertNotNull(javaParser);
        this.javaParser = javaParser;
        return this;
    }

    /**
     * An interface to define a callback for each file that's parsed.
     *
     */
    public interface Callback {

        /**
         * Process the given parse result.
         *
         * @param relativeZipEntryPath The relative path of the entry in the ZIP file that was parsed.
         * @param result The parse result of file located at <i>absolutePath</i>.
         */
        void process(Path relativeZipEntryPath, ParseResult<CompilationUnit> result);
    }
}
