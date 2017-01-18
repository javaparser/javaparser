package com.github.javaparser.generator.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.printer.PrettyPrinter;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.UTF8;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

/**
 * A collection of files located in one directory and its subdirectories on the file system.
 * Files can be parsed and written back one by one or all together.
 */
public class SourceRoot {
    public static final DataKey<Path> ORIGINAL_LOCATION = new DataKey<Path>() {
    };

    private final Path root;
    private final List<CompilationUnit> compilationUnits = new ArrayList<>();
    private final List<Problem> problems = new ArrayList<>();

    public SourceRoot(Path root) {
        this.root = root.normalize();
    }

    public void parse(String startPackage, JavaParser parser) throws IOException {
        Path path = packagePath(root, startPackage);
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

    public void saveAll() throws FileNotFoundException, UnsupportedEncodingException {
        for (CompilationUnit cu : compilationUnits) {
            Path filename = cu.getData(ORIGINAL_LOCATION);
            System.out.println("Saving " + filename);
            filename.getParent().toFile().mkdirs();
            String code = new PrettyPrinter().print(cu);
            try (PrintWriter out = new PrintWriter(filename.toFile(), UTF8.toString())) {
                out.println(code);
            }
        }
    }

    public List<Problem> getProblems() {
        return problems;
    }

    public List<CompilationUnit> getCompilationUnits() {
        return compilationUnits;
    }

    public Optional<CompilationUnit> parse(String packag, String filename, JavaParser javaParser) throws IOException {
        Path path = fileInPackagePath(root, packag, filename);
        System.out.println("Loading " + path);
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

    public void add(String pkg, String filename, CompilationUnit compilationUnit) {
        compilationUnits.add(compilationUnit);
        compilationUnit.setData(ORIGINAL_LOCATION, root.resolve(packageToPath(pkg)).resolve(filename));
    }
}
