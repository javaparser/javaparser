package com.github.javaparser.manual;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.validator.Java9Validator;
import com.github.javaparser.utils.CodeGenerationUtils;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;
import net.sourceforge.javadpkg.impl.DebianPackageParserImpl;
import org.junit.Test;
import org.redline_rpm.ReadableChannelWrapper;
import org.redline_rpm.Scanner;

import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.FileChannel;
import java.nio.channels.ReadableByteChannel;
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
        new BulkParseTest().parseOpenJdk();
    }

    private void parseOpenJdk() throws IOException {
        Path workdir = CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve(Paths.get(temporaryDirectory(), "javaparser_openjdk_download"));
        workdir.toFile().mkdirs();
        Path openJdkZipPath = workdir.resolve("openjdk.deb");
        if (Files.notExists(openJdkZipPath)) {
            Log.info("Downloading openjdk");
            download(new URL("http://nl.archive.ubuntu.com/ubuntu/pool/main/o/openjdk-8/openjdk-8-source_8u131-b11-2ubuntu1.17.04.3_all.deb"), openJdkZipPath);
        }
        new DebianPackageParserImpl();
        
//        if (Files.notExists(workdir.resolve("openjdk"))) {
//            Log.info("Unzipping openjdk");
//            unzip(openJdkZipPath, workdir);
//        }
//
//        bulkTest(new SourceRoot(workdir), "openjdk_test_results.txt");
    }

    @Test
    public void parseOwnSourceCode() throws IOException {
        bulkTest(new SourceRoot(CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve("..")), "javaparser_test_results.txt");
    }

    public void bulkTest(SourceRoot sourceRoot, String testResultsFileName) throws IOException {
        sourceRoot.setJavaParser(new JavaParser(new ParserConfiguration().setValidator(new Java9Validator())));
        Path testResults = CodeGenerationUtils.mavenModuleRoot(BulkParseTest.class).resolve(Paths.get("..", "javaparser-testing", "src", "test", "resources", "com", "github", "javaparser", "bulk_test_results")).normalize();
        testResults.toFile().mkdirs();
        testResults = testResults.resolve(testResultsFileName);
        TreeMap<Path, List<Problem>> results = new TreeMap<>(comparing(o -> o.toString().toLowerCase()));
        sourceRoot.parse("", new JavaParser(), (localPath, absolutePath, result) -> {
            if (!localPath.toString().contains("target")) {
                if (!result.isSuccessful()) {
                    results.put(localPath, result.getProblems());
                }
            }
            return DONT_SAVE;
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