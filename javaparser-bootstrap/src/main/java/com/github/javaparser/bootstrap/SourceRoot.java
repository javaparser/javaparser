package com.github.javaparser.bootstrap;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.printer.PrettyPrinter;

import java.io.*;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.Providers.*;

/**
 * A collection of files located in one directory and its subdirectories on the file system.
 * Files can be parsed and written back one by one or all together.
 */
public class SourceRoot {
    public static final DataKey<Path> ORIGINAL_LOCATION = new DataKey<Path>() {
    };

    private final Path root;
    private final Set<CompilationUnit> compilationUnits = new HashSet<>();
    private final List<Problem> problems = new ArrayList<>();

    public SourceRoot(Path root) {
        this.root = root.normalize();
    }

    public void parse(String startPackage, JavaParser parser) throws IOException {
        Path path = packagePath(startPackage);
        compilationUnits.clear();
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && file.toString().endsWith(".java")) {
                    parse(startPackage, file.getFileName().toString(), parser);
                }
                return FileVisitResult.CONTINUE;
            }
        });
    }

    private Path fileInPackagePath(String startPackage, String file) {
        startPackage = startPackage.replace(".", File.separator);
        return Paths.get(root.toString(), startPackage, file).normalize();
    }

    private Path packagePath(String startPackage) {
        startPackage = startPackage.replace(".", File.separator);
        return Paths.get(root.toString(), startPackage).normalize();
    }

    public void saveAll() throws FileNotFoundException, UnsupportedEncodingException {
        for (CompilationUnit cu : compilationUnits) {
            Path filename = cu.getData(ORIGINAL_LOCATION);
            String code = new PrettyPrinter().print(cu);
            try (PrintWriter out = new PrintWriter(filename.toFile(), UTF8.toString())) {
                out.println(code);
            }
        }
    }

    public List<Problem> getProblems() {
        return problems;
    }

    public Set<CompilationUnit> getCompilationUnits() {
        return compilationUnits;
    }

    public Optional<CompilationUnit> parse(String packag, String filename, JavaParser javaParser) throws IOException {
        Path path = fileInPackagePath(packag, filename);
        System.out.println(path);
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(path));
        if (result.isSuccessful()) {
            CompilationUnit cu = result.getResult().get();
            compilationUnits.add(cu);
            cu.setData(ORIGINAL_LOCATION, path);
        } else {
            problems.addAll(result.getProblems());
        }
        return result.getResult();
    }
}
