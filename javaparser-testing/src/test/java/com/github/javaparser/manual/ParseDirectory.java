package com.github.javaparser.manual;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.TokenMgrException;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

/**
 * Parses all files in a directory and its subdirectories.
 * 
 * The OpenJDK for example: http://download.java.net/openjdk/jdk8/
 * Or the source of JavaParser: .
 */
public class ParseDirectory {
    public static void main(String[] args) throws IOException {
        Files.find(new File(".").toPath(), 30, (path, basicFileAttributes) -> true).forEach(p -> {
            if (!Files.isDirectory(p) && p.toString().endsWith(".java")) {
                try {
                    System.out.print(p + "...");
                    JavaParser.parse(p.toFile());
                    System.out.println(" OK");
                } catch (TokenMgrException | ParseException | IOException e) {
                    System.out.println(" ERROR: " + e.getMessage());
                }
            }
        });
    }
}
