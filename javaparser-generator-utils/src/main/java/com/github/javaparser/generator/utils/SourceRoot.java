package com.github.javaparser.generator.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.PrettyPrinter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.UTF8;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

/**
 * A collection of Java source files located in one directory and its subdirectories on the file system.
 * Files can be parsed and written back one by one or all together.
 */
public class SourceRoot {
    private final Logger log = LoggerFactory.getLogger(SourceRoot.class);
    private final Path root;
    private final Map<Path, CompilationUnit> content = new HashMap<>();
    private final List<Problem> problems = new ArrayList<>();

    public SourceRoot(Path root) {
        this.root = root.normalize();
        log.info(f("New source root at \"%s\"", this.root));
    }

    /**
     * Parses a package recursively.
     */
    public Map<Path, CompilationUnit> parse(String startPackage, JavaParser parser) throws IOException {
        log.info(f("Parsing package \"%s\"", startPackage));
        final Path path = packageAbsolutePath(root, startPackage);
        content.clear();
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && file.toString().endsWith(".java")) {
                    parse(startPackage, file.getFileName().toString(), parser);
                }
                return FileVisitResult.CONTINUE;
            }
        });
        return content;
    }

    /**
     * Parse every Java file in this source root.
     */
    public Map<Path, CompilationUnit> parse(JavaParser parser) throws IOException {
        return parse("", parser);
    }

    /**
     * Save all files back to where they were found.
     */
    public void saveAll() throws FileNotFoundException, UnsupportedEncodingException {
        saveAll(root);
    }

    /**
     * Save all files back to another path.
     */
    public void saveAll(Path root) throws FileNotFoundException, UnsupportedEncodingException {
        log.info(f("Saving all files (%s) to %s", content.size(), root));
        for (Map.Entry<Path, CompilationUnit> cu : content.entrySet()) {
            final Path path = root.resolve(cu.getKey());
            log.debug(f("Saving %s", path));
            path.getParent().toFile().mkdirs();

            final String code = new PrettyPrinter().print(cu.getValue());
            try (PrintWriter out = new PrintWriter(path.toFile(), UTF8.toString())) {
                out.println(code);
            }
        }
    }

    /**
     * A complete list of encountered problems while parsing.
     */
    public List<Problem> getProblems() {
        return problems;
    }

    /**
     * The Java files that have been parsed by this source root object.
     */
    public Map<Path, CompilationUnit> getContent() {
        return content;
    }

    /**
     * Parse a single Java file and return it.
     */
    public Optional<CompilationUnit> parse(String packag, String filename, JavaParser javaParser) throws IOException {
        final Path relativePath = fileInPackageRelativePath(packag, filename);
        if (content.containsKey(relativePath)) {
            log.debug(f("Retrieving cached %s", relativePath));
            return Optional.of(content.get(relativePath));
        }
        final Path path = root.resolve(relativePath);
        log.debug(f("Parsing %s", path));
        final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(path));
        if (result.isSuccessful()) {
            final CompilationUnit cu = result.getResult().get();
            content.put(relativePath, cu);
        } else {
            log.error(f("Problems occurred parsing %s.", relativePath));
            problems.addAll(result.getProblems());
        }
        return result.getResult();
    }

    /**
     * Add a newly created Java file to this source root. It will be saved when saveAll is called.
     */
    public void add(String pkg, String filename, CompilationUnit compilationUnit) {
        log.debug(f("Adding new file %s.%s", pkg, filename));
        final Path path = fileInPackageRelativePath(pkg, filename);
        content.put(path, compilationUnit);
    }
}
