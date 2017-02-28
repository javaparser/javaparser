package com.github.javaparser.manual;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.CodeGenerationUtils;
import com.github.javaparser.utils.SourceRoot;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;

/**
 * Parses all files in a directory and its subdirectories.
 * <p>
 * The OpenJDK for example: http://download.java.net/openjdk/jdk8/
 * Or the source of JavaParser: .
 */
public class ParseDirectory {
    public static void main(String[] args) throws IOException {
        SourceRoot sourceRoot = new SourceRoot(CodeGenerationUtils.mavenModuleRoot());
//        sourceRoot.
        JavaParser parser = new JavaParser();
        Files.find(new File("/home/danny/tmp/openjdk/").toPath(), 30, (path, basicFileAttributes) -> true).forEach(p -> {
            if (!Files.isDirectory(p) && p.toString().endsWith(".java")) {
                try {
                    ParseResult<CompilationUnit> parse = parser.parse(COMPILATION_UNIT, provider(p));
                    if (parse.isSuccessful()) {
                        System.out.print(".");
                    } else {
                        System.out.println(p);
                        System.out.flush();
                        for (Problem problem : parse.getProblems()) {
                            System.err.println(problem.getMessage());
                        }
                        System.err.flush();
                    }
                } catch (Throwable e) {
                    System.out.println(" ERROR: " + e.getMessage());
                }
            }
        });
    }
}
