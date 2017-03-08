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
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static com.github.javaparser.utils.SourceRoot.Callback.Result.DONT_SAVE;
import static com.github.javaparser.utils.TestUtils.*;

public class BulkParseTest {
    /**
     * Running this will download a version of the OpenJDK,
     * unzip it, and parse it.
     * If it throws a stack overflow exception, increase the JVM's stack size.
     */
    public static void main(String[] args) throws IOException {
        new BulkParseTest().parseOpenJdk();
    }

    private void parseOpenJdk() throws IOException {
        Path workdir = CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve(Paths.get(temporaryDirectory(), "javaparser_openjdk_download"));
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
        bulkTest(new SourceRoot(CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve("..")), "javaparser_test_results.txt");
    }

    public void bulkTest(SourceRoot sourceRoot, String testResultsFileName) throws IOException {
        Path testResults = CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve(Paths.get("..", "javaparser-testing", "src", "test", "resources", "com", "github", "javaparser", "bulk_test_results")).normalize();
        testResults.toFile().mkdirs();
        testResults = testResults.resolve(testResultsFileName);
        TreeMap<Path, List<Problem>> results = new TreeMap<>();
        sourceRoot.parse("", new JavaParser(), (localPath, absolutePath, result) -> {
            if (!localPath.toString().contains("target")) {
                if (!result.isSuccessful()) {
                    results.put(localPath, result.getProblems());
                }
            }
            return DONT_SAVE;
        });
        Log.info("Writing results...");

        try (BufferedWriter writer = Files.newBufferedWriter(testResults)) {
            for (Map.Entry<Path, List<Problem>> file : results.entrySet()) {
                writer.write(file.getKey().toString().replace("\\", "/"));
                writer.newLine();
                for (Problem problem : file.getValue()) {
                    writer.write(problem.getVerboseMessage());
                    writer.newLine();
                }
                writer.newLine();
            }
        }

        Log.info("Results are in %s", testResults);
    }
}