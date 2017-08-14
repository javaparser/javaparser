package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.PrettyPrinter;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.CodeGenerationUtils.fileInPackageRelativePath;
import static com.github.javaparser.utils.CodeGenerationUtils.packageAbsolutePath;
import static com.github.javaparser.utils.SourceRoot.Callback.Result.SAVE;
import static com.github.javaparser.utils.Utils.*;

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
        Result process(Path localPath, Path absolutePath, ParseResult<CompilationUnit> result);
    }

    private final Path root;
    private final Map<Path, ParseResult<CompilationUnit>> cache = new HashMap<>();
    private JavaParser javaParser = new JavaParser();
    private Function<CompilationUnit, String> printer = new PrettyPrinter()::print; 

    public SourceRoot(Path root) {
        assertNotNull(root);
        if (!Files.isDirectory(root)) {
            throw new IllegalArgumentException("Only directories are allowed as root path!");
        }
        this.root = root.normalize();
        Log.info("New source root at \"%s\"", this.root);
    }

    /**
     * Tries to parse all .java files in a package recursively, and returns all files ever parsed with this source root. 
     * It keeps track of all parsed files so you can write them out with a single saveAll() call.
     * Note that the cache grows with every file parsed, 
     * so if you don't need saveAll(),
     * or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you might want to use
     * the parse method with a callback.
     */
    public List<ParseResult<CompilationUnit>> tryToParse(String startPackage) throws IOException {
        assertNotNull(startPackage);
        Log.info("Parsing package \"%s\"", startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && file.toString().endsWith(".java")) {
                    Path relative = root.relativize(file.getParent());
                    tryToParse(relative.toString(), file.getFileName().toString());
                }
                return FileVisitResult.CONTINUE;
            }
        });
        return getCache();
    }

    /**
     * Tries to parse all .java files in a package recursively and passes them one by one to the callback.
     * In comparison to the other parse methods, this is much more memory efficient,
     * but saveAll() won't work.
     */
    public SourceRoot parse(String startPackage, JavaParser javaParser, Callback callback) throws IOException {
        assertNotNull(startPackage);
        assertNotNull(javaParser);
        assertNotNull(callback);
        Log.info("Parsing package \"%s\"", startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path absolutePath, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && absolutePath.toString().endsWith(".java")) {
                    Path localPath = root.relativize(absolutePath);
                    Log.trace("Parsing %s", localPath);
                    final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(absolutePath));
                    result.getResult().ifPresent(cu -> cu.setStorage(absolutePath));
                    if (callback.process(localPath, absolutePath, result) == SAVE) {
                        if (result.getResult().isPresent()) {
                            save(result.getResult().get(), path);
                        }
                    }
                }
                return FileVisitResult.CONTINUE;
            }
        });
        return this;
    }

    /**
     * Tries to parse all .java files under the source root recursively, and returns all files ever parsed with this source root. 
     * It keeps track of all parsed files so you can write them out with a single saveAll() call.
     * Note that the cache grows with every file parsed, 
     * so if you don't need saveAll(),
     * or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you might want to use
     * the parse method with a callback.
     */
    public List<ParseResult<CompilationUnit>> tryToParse() throws IOException {
        return tryToParse("");
    }

    /**
     * Save all previously parsed files back to where they were found.
     */
    public SourceRoot saveAll() {
        return saveAll(root);
    }

    /**
     * Save all previously parsed files back to a new path.
     */
    public SourceRoot saveAll(Path root) {
        assertNotNull(root);
        Log.info("Saving all files (%s) to %s", cache.size(), root);
        for (Map.Entry<Path, ParseResult<CompilationUnit>> cu : cache.entrySet()) {
            final Path path = root.resolve(cu.getKey());
            if (cu.getValue().getResult().isPresent()) {
                Log.trace("Saving %s", path);
                save(cu.getValue().getResult().get(), path);
            }
        }
        return this;
    }

    private SourceRoot save(CompilationUnit cu, Path path) {
        assertNotNull(cu);
        assertNotNull(path);
        
        cu.setStorage(path);
        cu.getStorage().get().save(printer);
        return this;
    }

    /**
     * The Java files that have been parsed by this source root object,
     * or have been added manually.
     */
    public List<ParseResult<CompilationUnit>> getCache() {
        return new ArrayList<>(cache.values());
    }

    /**
     * The CompilationUnits of the Java files that have been parsed succesfully by this source root object,
     * or have been added manually.
     */
    public List<CompilationUnit> getCompilationUnits() {
        return cache.values().stream()
                .filter(ParseResult::isSuccessful)
                .map(p -> p.getResult().get())
                .collect(Collectors.toList());
    }

    /**
     * Tries to parse a .java files under the source root and returns the ParseResult. 
     * It keeps track of the parsed file so you can write it out with the saveAll() call.
     * Note that the cache grows with every file parsed,
     * so if you don't need saveAll(),
     * or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you might want to use
     * the parse method with a callback.
     */
    public ParseResult<CompilationUnit> tryToParse(String pkg, String filename) throws IOException {
        assertNotNull(pkg);
        assertNotNull(filename);
        final Path relativePath = fileInPackageRelativePath(pkg, filename);
        if (cache.containsKey(relativePath)) {
            Log.trace("Retrieving cached %s", relativePath);
            return cache.get(relativePath);
        }
        final Path path = root.resolve(relativePath);
        Log.trace("Parsing %s", path);
        final ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(path));
        result.getResult().ifPresent(cu -> cu.setStorage(path));
        cache.put(relativePath, result);
        return result;
    }

    /**
     * Parses a .java files under the source root and returns its CompilationUnit. 
     * It keeps track of the parsed file so you can write it out with the saveAll() call.
     * Note that the cache grows with every file parsed,
     * so if you don't need saveAll(),
     * or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you might want to use
     * the parse method with a callback.
     * 
     * @throws ParseProblemException when something went wrong.
     */
    public CompilationUnit parse(String pkg, String filename) {
        assertNotNull(pkg);
        assertNotNull(filename);
        try {
            final ParseResult<CompilationUnit> result = tryToParse(pkg, filename);
            if (result.isSuccessful()) {
                return result.getResult().get();
            }
            throw new ParseProblemException(result.getProblems());
        } catch (IOException e) {
            throw new ParseProblemException(e);
        }
    }

    /**
     * Add a newly created Java file to the cache of this source root. 
     * It will be saved when saveAll is called.
     */
    public SourceRoot add(String pkg, String filename, CompilationUnit compilationUnit) {
        assertNotNull(pkg);
        assertNotNull(filename);
        assertNotNull(compilationUnit);
        Log.trace("Adding new file %s.%s", pkg, filename);
        final Path path = fileInPackageRelativePath(pkg, filename);
        final ParseResult<CompilationUnit> parseResult = new ParseResult<>(compilationUnit, new ArrayList<>(), null, null);
        cache.put(path, parseResult);
        return this;
    }

    /**
     * Add a newly created Java file to the cache of this source root. 
     * It will be saved when saveAll is called.
     * It needs to have its path set.
     */
    public SourceRoot add(CompilationUnit compilationUnit) {
        assertNotNull(compilationUnit);
        if (compilationUnit.getStorage().isPresent()) {
            final Path path = compilationUnit.getStorage().get().getPath();
            Log.trace("Adding new file %s", path);
            final ParseResult<CompilationUnit> parseResult = new ParseResult<>(compilationUnit, new ArrayList<>(), null, null);
            cache.put(path, parseResult);
        } else {
            throw new AssertionError("Files added with this method should have their path set.");
        }
        return this;
    }

    /**
     * The path that was passed in the constructor.
     */
    public Path getRoot() {
        return root;
    }

    public JavaParser getJavaParser() {
        return javaParser;
    }

    /**
     * Set the parser that is used for parsing by default.
     */
    public SourceRoot setJavaParser(JavaParser javaParser) {
        assertNotNull(javaParser);
        this.javaParser = javaParser;
        return this;
    }

    /**
     * Set the printing function that transforms compilation units into a string to save.
     */
    public SourceRoot setPrinter(Function<CompilationUnit, String> printer) {
        assertNotNull(printer);
        this.printer = printer;
        return this;
    }

    public Function<CompilationUnit, String> getPrinter() {
        return printer;
    }
}
