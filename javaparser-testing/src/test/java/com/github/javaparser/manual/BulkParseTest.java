package com.github.javaparser.manual;

import com.github.javaparser.JavaParser;
import com.github.javaparser.Problem;
import com.github.javaparser.utils.CodeGenerationUtils;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;
import org.junit.Test;

import java.io.BufferedWriter;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static com.github.javaparser.utils.SourceRoot.Callback.Result.DONT_SAVE;
import static com.github.javaparser.utils.TestUtils.download;
import static com.github.javaparser.utils.TestUtils.unzip;

public class BulkParseTest {
    /**
     * Running this will download a version of the OpenJDK,
     * unzip it, and parse it.
     */
    public static void main(String[] args) throws IOException {
        new BulkParseTest().parseOpenJdk();
    }

    private void parseOpenJdk() throws IOException {
        Path workdir = CodeGenerationUtils.mavenModuleRoot().resolve(Paths.get("target", "tmp"));
        workdir.toFile().mkdirs();
        Path openJdkZipPath = workdir.resolve("openjdk.zip");
        if (Files.notExists(openJdkZipPath)) {
            Log.info("Downloading openjdk");
            download(new URL("https://home.java.net/download/openjdk/jdk8/promoted/b132/openjdk-8-src-b132-03_mar_2014.zip"), openJdkZipPath);
        }
        if (Files.notExists(workdir.resolve("openjdk"))) {
            Log.info("Unzipping openjdk");
            unzip(openJdkZipPath, workdir);
        }

        bulkTest(new SourceRoot(workdir), "openjdk_test_results.txt");
    }

    @Test
    public void parseOwnSourceCode() throws IOException {
        bulkTest(new SourceRoot(CodeGenerationUtils.mavenModuleRoot().resolve("..")), "javaparser_test_results.txt");
    }

    public void bulkTest(SourceRoot sourceRoot, String testResultsFileName) throws IOException {
        Path testResults = CodeGenerationUtils.mavenModuleRoot().resolve(Paths.get("..", "javaparser-testing", "src", "test", "resources", "com", "github", "javaparser", "bulk_test_results")).normalize();
        testResults.toFile().mkdirs();
        testResults = testResults.resolve(testResultsFileName);
        try (BufferedWriter writer = Files.newBufferedWriter(testResults)) {
            sourceRoot.parse("", new JavaParser(), (localPath, absolutePath, result) -> {
                if (!result.isSuccessful()) {
                    writer.write(localPath.toString());
                    writer.newLine();
                    for (Problem problem : result.getProblems()) {
                        writer.write(problem.getMessage());
                        writer.newLine();
                    }
                }
                return DONT_SAVE;
            });
        }
        Log.info("Results are in %s", testResults);
    }
}