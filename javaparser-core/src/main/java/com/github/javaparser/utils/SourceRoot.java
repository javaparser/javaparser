package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.PrettyPrinter;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.UTF8;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.CodeGenerationUtils.fileInPackageRelativePath;
import static com.github.javaparser.utils.CodeGenerationUtils.packageAbsolutePath;
import static com.github.javaparser.utils.SourceRoot.Callback.Result.SAVE;

/**
 * A collection of Java source files located in one directory and its subdirectories on the file system.
 * Files can be parsed and written back one by one or all together.
 */
public class SourceRoot {
    public interface Callback {
        enum Result {SAVE, DONT_SAVE}

        /**
         * @param localPath the path to the file that was parsed, relative to the source root path.
         * @param absolutePath the absolute path to the file that was parsed.
         * @param result the result of of parsing the file.
         */
        Result process(Path localPath, Path absolutePath, ParseResult<CompilationUnit> result) throws IOException;
    }

    private final Path root;
    private final Map<Path, ParseResult<CompilationUnit>> content = new HashMap<>();

    public SourceRoot(Path root) {
        this.root = root.normalize();
        Log.info("New source root at \"%s\"", this.root);
    }

    /**
     * Parses all .java files in a package recursively, caches them, and returns all files ever parsed with this source
     * root.
     */
    public Map<Path, ParseResult<CompilationUnit>> tryToParse(String startPackage, JavaParser parser) throws IOException {
        Log.info("Parsing package \"%s\"", startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && file.toString().endsWith(".java")) {
                    tryToParse(startPackage, file.getFileName().toString(), parser);
                }
                return FileVisitResult.CONTINUE;
            }
        });
        return content;
    }

    /**
     * Parses a package recursively with a callback.
     * The advantage: it doesn't keep all files and AST's in memory.
     * The disadvantage: you have to do your processing directly.
     */
    public void parse(String startPackage, JavaParser javaParser, Callback callback) throws IOException {
        Log.info("Parsing package \"%s\"", startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path absolutePath, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && absolutePath.toString().endsWith(".java")) {
                    Path localPath = root.relativize(absolutePath);
                    Log.trace("Parsing %s", localPath);
                    final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(absolutePath));
                    if (callback.process(localPath, absolutePath, result) == SAVE) {
                        if (result.getResult().isPresent()) {
                            save(result.getResult().get(), path);
                        }
                    }
                }
                return FileVisitResult.CONTINUE;
            }
        });
    }

    /**
     * Parse every .java file in this source root.
     */
    public Map<Path, ParseResult<CompilationUnit>> tryToParse(JavaParser parser) throws IOException {
        return tryToParse("", parser);
    }

    /**
     * Save all files back to where they were found.
     */
    public void saveAll() throws IOException {
        saveAll(root);
    }

    /**
     * Save all files back to another path.
     */
    public void saveAll(Path root) throws IOException {
        Log.info("Saving all files (%s) to %s", content.size(), root);
        for (Map.Entry<Path, ParseResult<CompilationUnit>> cu : content.entrySet()) {
            final Path path = root.resolve(cu.getKey());
            if (cu.getValue().getResult().isPresent()) {
                Log.trace("Saving %s", path);
                save(cu.getValue().getResult().get(), path);
            }
        }
    }

    private void save(CompilationUnit cu, Path path) throws IOException {
        path.getParent().toFile().mkdirs();

        final String code = new PrettyPrinter().print(cu);
        try (PrintWriter out = new PrintWriter(path.toFile(), UTF8.toString())) {
            out.println(code);
        } catch (UnsupportedEncodingException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * The Java files that have been parsed by this source root object,
     * or have been added manually.
     */
    public Map<Path, ParseResult<CompilationUnit>> getContent() {
        return content;
    }

    /**
     * The CompilationUnits of the Java files that have been parsed succesfully by this source root object,
     * or have been added manually.
     */
    public List<CompilationUnit> getCompilationUnits() {
        return content.values().stream()
                .filter(ParseResult::isSuccessful)
                .map(p -> p.getResult().get())
                .collect(Collectors.toList());
    }

    /**
     * Try to parse a single Java file and return the result of parsing.
     */
    public ParseResult<CompilationUnit> tryToParse(String packag, String filename, JavaParser javaParser) throws IOException {
        final Path relativePath = fileInPackageRelativePath(packag, filename);
        if (content.containsKey(relativePath)) {
            Log.trace("Retrieving cached %s", relativePath);
            return content.get(relativePath);
        }
        final Path path = root.resolve(relativePath);
        Log.trace("Parsing %s", path);
        final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(path));
        content.put(relativePath, result);
        return result;
    }

    /**
     * Try to parse a single Java file and return it.
     *
     * @throws ParseProblemException when something went wrong.
     */
    public CompilationUnit parse(String packag, String filename, JavaParser javaParser) {
        try {
            ParseResult<CompilationUnit> result = tryToParse(packag, filename, javaParser);
            if (result.isSuccessful()) {
                return result.getResult().get();
            }
            throw new ParseProblemException(result.getProblems());
        } catch (IOException e) {
            throw new ParseProblemException(e);
        }
    }

    /**
     * Add a newly created Java file to this source root. It will be saved when saveAll is called.
     */
    public void add(String pkg, String filename, CompilationUnit compilationUnit) {
        Log.trace("Adding new file %s.%s", pkg, filename);
        final Path path = fileInPackageRelativePath(pkg, filename);
        final ParseResult<CompilationUnit> parseResult = new ParseResult<>(compilationUnit, new ArrayList<>(), null, null);
        content.put(path, parseResult);
    }

    /**
     * The path that was passed in the constructor.
     */
    public Path getRoot() {
        return root;
    }
}
