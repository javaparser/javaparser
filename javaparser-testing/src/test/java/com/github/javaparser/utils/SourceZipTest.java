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

import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.TestUtils.download;
import static com.github.javaparser.utils.TestUtils.temporaryDirectory;
import static com.github.javaparser.utils.TestUtils.unzip;
import static java.util.Comparator.comparing;

import java.io.BufferedWriter;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.validator.Java9Validator;

public class SourceZipTest {

    private final static String ZIP_URL = "https://github.com/javaparser/javaparser/archive/master.zip";
    private final static String ZIP_DOWNLOAD_DIR = "javaparser_download";
    private final static String ZIP_NAME = "master.zip";

    @Test
    private void parseJavaParserSourceZip() throws IOException {
        Path workdir = CodeGenerationUtils.mavenModuleRoot(SourceZipTest.class)
                .resolve(Paths.get(temporaryDirectory(), ZIP_DOWNLOAD_DIR));
        workdir.toFile().mkdirs();
        Path javaParserZipPath = workdir.resolve(ZIP_NAME);
        if (Files.notExists(javaParserZipPath)) {
            Log.info("Downloading JavaParser");
            download(
                    new URL(ZIP_URL),
                    javaParserZipPath);
        }
        if (Files.notExists(workdir.resolve("master"))) {
            Log.info("Unzipping JavaParser");
            unzip(javaParserZipPath, workdir);
        }
        bulkTest(new SourceZip(workdir), "javaparser_test_results.txt");
    }

    private void bulkTest(SourceZip sourceZip, String testResultsFileName) throws IOException {
        sourceZip.setJavaParser(new JavaParser(new ParserConfiguration().setValidator(new Java9Validator())));
        Path testResults = CodeGenerationUtils.mavenModuleRoot(SourceZipTest.class).resolve(Paths.get("..",
                "javaparser-testing", "src", "test", "resources", "com", "github", "javaparser", "bulk_test_results"))
                .normalize();
        testResults.toFile().mkdirs();
        testResults = testResults.resolve(testResultsFileName);
        TreeMap<Path, List<Problem>> results = new TreeMap<>(comparing(o -> o.toString().toLowerCase()));
        sourceZip.parse((zipPath, relativeFilePath, result) -> {
            if (!relativeFilePath.toString().contains("target")) {
                if (!result.isSuccessful()) {
                    results.put(relativeFilePath, result.getProblems());
                }
            }
        });
        Log.info("Writing results...");

        int problemTotal = 0;
        try (BufferedWriter writer = Files.newBufferedWriter(testResults)) {
            for (Map.Entry<Path, List<Problem>> file : results.entrySet()) {
                writer.write(file.getKey().toString().replace("\\", "/"));
                writer.newLine();
                for (Problem problem : file.getValue()) {
                    writer.write(problem.getVerboseMessage());
                    writer.newLine();
                    problemTotal++;
                }
                writer.newLine();
            }
            writer.write(f("%s problems in %s files", problemTotal, results.size()));
        }

        Log.info("Results are in %s", testResults);
    }

}
