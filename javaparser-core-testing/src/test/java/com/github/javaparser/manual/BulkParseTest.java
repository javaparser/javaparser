/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.manual;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.CodeGenerationUtils.mavenModuleRoot;
import static com.github.javaparser.utils.SourceRoot.Callback.Result.DONT_SAVE;
import static java.util.Comparator.comparing;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;
import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class BulkParseTest {
    @BeforeEach
    void startLogging() {
        Log.setAdapter(new Log.StandardOutStandardErrorAdapter());
    }

    @AfterEach
    void stopLogging() {
        Log.setAdapter(new Log.SilentAdapter());
    }

    @Test
    void parseOwnSourceCode() throws IOException {
        String[] roots = new String[] {
            "javaparser-core/src/main/java",
            "javaparser-core-testing/src/test/java",
            "javaparser-core-generators/src/main/java",
            "javaparser-core-metamodel-generator/src/main/java",
            "javaparser-symbol-solver-core/src/main/java",
            "javaparser-symbol-solver-testing/src/test/java"
        };
        for (String root : roots) {
            bulkTest(
                    new SourceRoot(
                            mavenModuleRoot(BulkParseTest.class).resolve("..").resolve(root)),
                    "javaparser_test_results_" + root.replace("-", "_").replace("/", "_") + ".txt",
                    new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE));
        }
    }

    public void bulkTest(SourceRoot sourceRoot, String testResultsFileName, ParserConfiguration configuration)
            throws IOException {
        sourceRoot.setParserConfiguration(configuration);
        TreeMap<Path, List<Problem>> results =
                new TreeMap<>(comparing(o -> o.toString().toLowerCase()));
        sourceRoot.parseParallelized((localPath, absolutePath, result) -> {
            if (!localPath.toString().contains("target")) {
                if (!result.isSuccessful()) {
                    results.put(localPath, result.getProblems());
                }
            }
            return DONT_SAVE;
        });
        writeResults(results, testResultsFileName);
    }

    private void writeResults(TreeMap<Path, List<Problem>> results, String testResultsFileName) throws IOException {
        Log.info("Writing results...");

        Path testResults = mavenModuleRoot(BulkParseTest.class)
                .resolve("target")
                .resolve("bulk_test_results")
                .normalize();
        testResults.toFile().mkdirs();
        testResults = testResults.resolve(testResultsFileName);

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

        Path finalTestResults = testResults;
        Log.info("Results are in %s", () -> finalTestResults);

        assertEquals(
                0, problemTotal, f("%s parse problems in %s files, see %s", problemTotal, results.size(), testResults));
    }
}
