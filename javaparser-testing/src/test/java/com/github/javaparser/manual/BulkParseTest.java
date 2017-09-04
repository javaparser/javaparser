package com.github.javaparser.manual;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.validator.Java9Validator;
import com.github.javaparser.utils.CodeGenerationUtils;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;
import com.github.javaparser.utils.SourceZip;
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

import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.SourceRoot.Callback.Result.DONT_SAVE;
import static com.github.javaparser.utils.TestUtils.*;
import static java.util.Comparator.comparing;

public class BulkParseTest {
    /**
     * Running this will download a version of the OpenJDK, unzip it, and parse it. If it throws a stack overflow
     * exception, increase the JVM's stack size.
     */
    public static void main(String[] args) throws IOException {
        new BulkParseTest().parseJdkSrcZip();
    }

    private void parseOpenJdkSourceRepository() throws IOException {
        Path workdir = CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve(Paths.get(temporaryDirectory(), "javaparser_openjdk_download"));
        workdir.toFile().mkdirs();
        Path openJdkZipPath = workdir.resolve("openjdk.zip");
        if (Files.notExists(openJdkZipPath)) {
            Log.info("Downloading openjdk");
            // FIXME this file is lost :-(
            download(new URL("https://home.java.net/download/openjdk/jdk8/promoted/b132/openjdk-8-src-b132-03_mar_2014.zip"), openJdkZipPath);
        }
        if (Files.notExists(workdir.resolve("openjdk"))) {
            Log.info("Unzipping openjdk");
            unzip(openJdkZipPath, workdir);
        }

        bulkTest(new SourceRoot(workdir), "openjdk_src_repo_test_results.txt");
    }

    private void parseJdkSrcZip() throws IOException {
        // This is where Ubuntu stores the contents of package openjdk-8-src
        Path path = Paths.get("/usr/lib/jvm/openjdk-8/src.zip");
        bulkTest(new SourceZip(path), "openjdk_src_zip_test_results.txt");
    }

    @Test
    public void parseOwnSourceCode() throws IOException {
        bulkTest(new SourceRoot(CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve("..")), "javaparser_test_results.txt");
    }

    public void bulkTest(SourceRoot sourceRoot, String testResultsFileName) throws IOException {
        sourceRoot.setJavaParser(new JavaParser(new ParserConfiguration().setValidator(new Java9Validator())));
        TreeMap<Path, List<Problem>> results = new TreeMap<>(comparing(o -> o.toString().toLowerCase()));
        sourceRoot.parse("", new JavaParser(), (localPath, absolutePath, result) -> {
            if (!localPath.toString().contains("target")) {
                if (!result.isSuccessful()) {
                    results.put(localPath, result.getProblems());
                }
            }
            return DONT_SAVE;
        });
        writeResults(results, testResultsFileName);
    }

    public void bulkTest(SourceZip sourceRoot, String testResultsFileName) throws IOException {
        sourceRoot.setJavaParser(new JavaParser(new ParserConfiguration().setValidator(new Java9Validator())));
        TreeMap<Path, List<Problem>> results = new TreeMap<>(comparing(o -> o.toString().toLowerCase()));
        sourceRoot.parse((path, result) -> {
            if (!path.toString().contains("target")) {
                if (!result.isSuccessful()) {
                    results.put(path, result.getProblems());
                }
            }
        });
        writeResults(results, testResultsFileName);
    }

    private void writeResults(TreeMap<Path, List<Problem>> results, String testResultsFileName) throws IOException {
        Log.info("Writing results...");

        Path testResults = CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve(Paths.get("..", "javaparser-testing", "src", "test", "resources", "com", "github", "javaparser", "bulk_test_results")).normalize();
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

        Log.info("Results are in %s", testResults);
    }
}