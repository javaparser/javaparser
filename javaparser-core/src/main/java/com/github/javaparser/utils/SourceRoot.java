package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.PrettyPrinter;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveAction;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.CodeGenerationUtils.*;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.nio.file.FileVisitResult.*;

/**
 * A collection of Java source files located in one directory and its subdirectories on the file system. The root directory
 * corresponds to the root of the package structure of the source files within. Files can be parsed and written back one
 * by one or all together. <b>Note that</b> the internal cache used is thread-safe.
 * <ul>
 * <li>methods called "tryToParse..." will return their result inside a "ParseResult", which supports parse successes and failures.</li>
 * <li>methods called "parse..." will return "CompilationUnit"s. If a file fails to parse, an exception is thrown.</li>
 * <li>methods ending in "...Parallelized" will speed up parsing by using multiple threads.</li>
 * </ul>
 */
public class SourceRoot {
    @FunctionalInterface
    public interface Callback {
        enum Result {
            SAVE, DONT_SAVE, TERMINATE
        }

        /**
         * @param localPath the path to the file that was parsed, relative to the source root path.
         * @param absolutePath the absolute path to the file that was parsed.
         * @param result the result of of parsing the file.
         */
        Result process(Path localPath, Path absolutePath, ParseResult<CompilationUnit> result);
    }

    private final Path root;
    private final Map<Path, ParseResult<CompilationUnit>> cache = new ConcurrentHashMap<>();
    private ParserConfiguration parserConfiguration = new ParserConfiguration();
    private Function<CompilationUnit, String> printer = new PrettyPrinter()::print;
    private static final Pattern JAVA_IDENTIFIER = Pattern.compile("\\p{javaJavaIdentifierStart}\\p{javaJavaIdentifierPart}*");

    /**
     * @param root the root directory of a set of source files. It corresponds to the root of the package structure of the
     * source files within, like "javaparser/javaparser-core/src/main/java"
     */
    public SourceRoot(Path root) {
        assertNotNull(root);
        if (!Files.isDirectory(root)) {
            throw new IllegalArgumentException("Only directories are allowed as root path: " + root);
        }
        this.root = root.normalize();
        Log.info("New source root at \"%s\"", () -> this.root);
    }

    /**
     * @param root the root directory of a set of source files. It corresponds to the root of the package structure of the
     * source files within, like "javaparser/javaparser-core/src/main/java"
     */
    public SourceRoot(Path root, ParserConfiguration parserConfiguration) {
        this(root);
        setParserConfiguration(parserConfiguration);
    }

    /**
     * Tries to parse a .java files under the source root and returns the ParseResult. It keeps track of the parsed file
     * so you can write it out with the saveAll() call. Note that the cache grows with every file parsed, so if you
     * don't need saveAll(), or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you
     * might want to use the parse method with a callback.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public ParseResult<CompilationUnit> tryToParse(String startPackage, String filename, ParserConfiguration configuration) throws IOException {
        assertNotNull(startPackage);
        assertNotNull(filename);
        final Path relativePath = fileInPackageRelativePath(startPackage, filename);
        if (cache.containsKey(relativePath)) {
            Log.trace("Retrieving cached %s", () -> relativePath);
            return cache.get(relativePath);
        }
        final Path path = root.resolve(relativePath);
        Log.trace("Parsing %s", () -> path);
        final ParseResult<CompilationUnit> result = new JavaParser(configuration)
                .parse(COMPILATION_UNIT, provider(path, configuration.getCharacterEncoding()));
        result.getResult().ifPresent(cu -> cu.setStorage(path, configuration.getCharacterEncoding()));
        cache.put(relativePath, result);
        return result;
    }

    /**
     * Tries to parse a .java files under the source root and returns the ParseResult. It keeps track of the parsed file
     * so you can write it out with the saveAll() call. Note that the cache grows with every file parsed, so if you
     * don't need saveAll(), or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you
     * might want to use the parse method with a callback.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public ParseResult<CompilationUnit> tryToParse(String startPackage, String filename) throws IOException {
        return tryToParse(startPackage, filename, parserConfiguration);
    }

    /**
     * Tries to parse all .java files in a package recursively, and returns all files ever parsed with this source root.
     * It keeps track of all parsed files so you can write them out with a single saveAll() call. Note that the cache
     * grows with every file parsed, so if you don't need saveAll(), or you don't ask SourceRoot to parse files multiple
     * times (where the cache is useful) you might want to use the parse method with a callback.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public List<ParseResult<CompilationUnit>> tryToParse(String startPackage) throws IOException {
        assertNotNull(startPackage);
        logPackage(startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (!attrs.isDirectory() && file.toString().endsWith(".java")) {
                    Path relative = root.relativize(file.getParent());
                    tryToParse(relative.toString(), file.getFileName().toString());
                }
                return CONTINUE;
            }

            @Override
            public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                return isSensibleDirectoryToEnter(dir) ? CONTINUE : SKIP_SUBTREE;
            }
        });
        return getCache();
    }

    private static boolean isSensibleDirectoryToEnter(Path dir) throws IOException {
        final String dirToEnter = dir.getFileName().toString();
        // Don't enter directories that cannot be packages.
        final boolean directoryIsAValidJavaIdentifier = JAVA_IDENTIFIER.matcher(dirToEnter).matches();
        // Don't enter directories that are hidden, assuming that people don't store source files in hidden directories.
        if (Files.isHidden(dir) || !directoryIsAValidJavaIdentifier) {
            Log.trace("Not processing directory \"%s\"", () -> dirToEnter);
            return false;
        }
        return true;
    }

    /**
     * Tries to parse all .java files under the source root recursively, and returns all files ever parsed with this
     * source root. It keeps track of all parsed files so you can write them out with a single saveAll() call. Note that
     * the cache grows with every file parsed, so if you don't need saveAll(), or you don't ask SourceRoot to parse
     * files multiple times (where the cache is useful) you might want to use the parse method with a callback.
     */
    public List<ParseResult<CompilationUnit>> tryToParse() throws IOException {
        return tryToParse("");
    }

    /**
     * Tries to parse all .java files in a package recursively using multiple threads, and returns all files ever parsed
     * with this source root. A new thread is forked each time a new directory is visited and is responsible for parsing
     * all .java files in that directory. <b>Note that</b> to ensure thread safety, a new parser instance is created for
     * every file with the internal parser's (i.e. {@link #setParserConfiguration(ParserConfiguration)}) configuration.
     * It keeps track of all parsed files so you can write them out with a single saveAll() call.
     * Note that the cache grows with every file parsed,
     * so if you don't need saveAll(), or you don't ask SourceRoot to parse files multiple times (where the cache is
     * useful) you might want to use the parse method with a callback.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public List<ParseResult<CompilationUnit>> tryToParseParallelized(String startPackage) {
        assertNotNull(startPackage);
        logPackage(startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        ParallelParse parse = new ParallelParse(path, (file, attrs) -> {
            if (!attrs.isDirectory() && file.toString().endsWith(".java")) {
                Path relative = root.relativize(file.getParent());
                try {
                    tryToParse(
                            relative.toString(),
                            file.getFileName().toString(),
                            parserConfiguration);
                } catch (IOException e) {
                    Log.error(e);
                }
            }
            return CONTINUE;
        });
        ForkJoinPool pool = new ForkJoinPool();
        pool.invoke(parse);
        return getCache();
    }

    /**
     * Tries to parse all .java files under the source root recursively using multiple threads, and returns all files
     * ever parsed with this source root. A new thread is forked each time a new directory is visited and is responsible
     * for parsing all .java files in that directory. <b>Note that</b> to ensure thread safety, a new parser instance is
     * created for every file with the internal (i.e. {@link #setParserConfiguration(ParserConfiguration)}) configuration. It keeps track of
     * all parsed files so you can write them out with a single saveAll() call. Note that the cache grows with every
     * file parsed, so if you don't need saveAll(), or you don't ask SourceRoot to parse files multiple times (where the
     * cache is useful) you might want to use the parse method with a callback.
     */
    public List<ParseResult<CompilationUnit>> tryToParseParallelized() {
        return tryToParseParallelized("");
    }

    /**
     * Parses a .java files under the source root and returns its CompilationUnit. It keeps track of the parsed file so
     * you can write it out with the saveAll() call. Note that the cache grows with every file parsed, so if you don't
     * need saveAll(), or you don't ask SourceRoot to parse files multiple times (where the cache is useful) you might
     * want to use the parse method with a callback.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     * @throws ParseProblemException when something went wrong.
     */
    public CompilationUnit parse(String startPackage, String filename) {
        assertNotNull(startPackage);
        assertNotNull(filename);
        try {
            final ParseResult<CompilationUnit> result = tryToParse(startPackage, filename);
            if (result.isSuccessful()) {
                return result.getResult().get();
            }
            throw new ParseProblemException(result.getProblems());
        } catch (IOException e) {
            throw new ParseProblemException(e);
        }
    }

    private FileVisitResult callback(Path absolutePath, ParserConfiguration configuration, Callback callback) throws IOException {
        Path localPath = root.relativize(absolutePath);
        Log.trace("Parsing %s", () -> localPath);
        ParseResult<CompilationUnit> result = new JavaParser(configuration).parse(COMPILATION_UNIT, provider(absolutePath));
        result.getResult().ifPresent(cu -> cu.setStorage(absolutePath, configuration.getCharacterEncoding()));
        switch (callback.process(localPath, absolutePath, result)) {
            case SAVE:
                result.getResult().ifPresent(cu -> save(cu, absolutePath));
            case DONT_SAVE:
                return CONTINUE;
            case TERMINATE:
                return TERMINATE;
            default:
                throw new AssertionError("Return an enum defined in SourceRoot.Callback.Result");
        }
    }

    /**
     * Locates the .java file with the provided package and file name, parses it and passes it to the
     * callback. In comparison to the other parse methods, this is much more memory efficient, but saveAll() won't work.
     *
     * @param startPackage The package containing the file
     * @param filename The name of the file
     */
    public SourceRoot parse(String startPackage, String filename, ParserConfiguration configuration, Callback
            callback) throws IOException {
        assertNotNull(startPackage);
        assertNotNull(filename);
        assertNotNull(configuration);
        assertNotNull(callback);
        callback(fileInPackageAbsolutePath(root, startPackage, filename), configuration, callback);
        return this;
    }

    /**
     * Parses the provided .java file and passes it to the callback. In comparison to the other parse methods, this
     * makes is much more memory efficient., but saveAll() won't work.
     */
    public SourceRoot parse(String startPackage, String filename, Callback callback) throws IOException {
        parse(startPackage, filename, parserConfiguration, callback);
        return this;
    }

    /**
     * Tries to parse all .java files in a package recursively and passes them one by one to the callback. In comparison
     * to the other parse methods, this is much more memory efficient, but saveAll() won't work.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public SourceRoot parse(String startPackage, ParserConfiguration configuration, Callback callback) throws IOException {
        assertNotNull(startPackage);
        assertNotNull(configuration);
        assertNotNull(callback);
        logPackage(startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        if (Files.exists(path)) {
            Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
                @Override
                public FileVisitResult visitFile(Path absolutePath, BasicFileAttributes attrs) throws IOException {
                    if (!attrs.isDirectory() && absolutePath.toString().endsWith(".java")) {
                        return callback(absolutePath, configuration, callback);
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                    return isSensibleDirectoryToEnter(dir) ? CONTINUE : SKIP_SUBTREE;
                }
            });
        }
        return this;
    }

    public SourceRoot parse(String startPackage, Callback callback) throws IOException {
        parse(startPackage, parserConfiguration, callback);
        return this;
    }

    private void logPackage(String startPackage) {
        if (startPackage.isEmpty()) {
            return;
        }
        Log.info("Parsing package \"%s\"", () -> startPackage);
    }

    /**
     * Tries to parse all .java files in a package recursively using multiple threads, and passes them one by one to the
     * callback. A new thread is forked each time a new directory is visited and is responsible for parsing all .java
     * files in that directory. <b>Note that</b> the provided {@link Callback} code must be made thread-safe. <b>Note
     * that</b> to ensure thread safety, a new parser instance is created for every file with the provided {@link
     * ParserConfiguration}. In comparison to the other parse methods, this is much more memory efficient, but saveAll()
     * won't work.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public SourceRoot parseParallelized(String startPackage, ParserConfiguration configuration, Callback callback) {
        assertNotNull(startPackage);
        assertNotNull(configuration);
        assertNotNull(callback);
        logPackage(startPackage);
        final Path path = packageAbsolutePath(root, startPackage);
        if (Files.exists(path)) {
            ParallelParse parse = new ParallelParse(path, (absolutePath, attrs) -> {
                if (!attrs.isDirectory() && absolutePath.toString().endsWith(".java")) {
                    try {
                        return callback(absolutePath, configuration, callback);
                    } catch (IOException e) {
                        Log.error(e);
                    }
                }
                return CONTINUE;
            });
            ForkJoinPool pool = new ForkJoinPool();
            pool.invoke(parse);
        }
        return this;
    }

    /**
     * Tries to parse all .java files in a package recursively using multiple threads, and passes them one by one to the
     * callback. A new thread is forked each time a new directory is visited and is responsible for parsing all .java
     * files in that directory. <b>Note that</b> the provided {@link Callback} code must be made thread-safe. <b>Note
     * that</b> to ensure thread safety, a new parser instance is created for every file. In comparison to the other
     * parse methods, this is much more memory efficient, but saveAll() won't work.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public SourceRoot parseParallelized(String startPackage, Callback callback) throws IOException {
        return parseParallelized(startPackage, new ParserConfiguration(), callback);
    }

    /**
     * Tries to parse all .java files recursively using multiple threads, and passes them one by one to the callback. A
     * new thread is forked each time a new directory is visited and is responsible for parsing all .java files in that
     * directory. <b>Note that</b> the provided {@link Callback} code must be made thread-safe. <b>Note that</b> to
     * ensure thread safety, a new parser instance is created for every file. In comparison to the other parse methods,
     * this is much more memory efficient, but saveAll() won't work.
     */
    public SourceRoot parseParallelized(Callback callback) throws IOException {
        return parseParallelized("", new ParserConfiguration(), callback);
    }

    /**
     * Add a newly created Java file to the cache of this source root. It will be saved when saveAll is called.
     *
     * @param startPackage files in this package and deeper are parsed. Pass "" to parse all files.
     */
    public SourceRoot add(String startPackage, String filename, CompilationUnit compilationUnit) {
        assertNotNull(startPackage);
        assertNotNull(filename);
        assertNotNull(compilationUnit);
        Log.trace("Adding new file %s.%s", () -> startPackage, () -> filename);
        final Path path = fileInPackageRelativePath(startPackage, filename);
        final ParseResult<CompilationUnit> parseResult = new ParseResult<>(
                compilationUnit,
                new ArrayList<>(),
                null);
        cache.put(path, parseResult);
        return this;
    }

    /**
     * Add a newly created Java file to the cache of this source root. It will be saved when saveAll is called. It needs
     * to have its path set.
     */
    public SourceRoot add(CompilationUnit compilationUnit) {
        assertNotNull(compilationUnit);
        if (compilationUnit.getStorage().isPresent()) {
            final Path path = compilationUnit.getStorage().get().getPath();
            Log.trace("Adding new file %s", () -> path);
            final ParseResult<CompilationUnit> parseResult = new ParseResult<>(
                    compilationUnit,
                    new ArrayList<>(),
                    null);
            cache.put(path, parseResult);
        } else {
            throw new AssertionError("Files added with this method should have their path set.");
        }
        return this;
    }

    /**
     * Save the given compilation unit to the given path.
     * @param cu the compilation unit
     * @param path the path of the java file
     */
    private SourceRoot save(CompilationUnit cu, Path path) {
        return save(cu, path, parserConfiguration.getCharacterEncoding());
    }

    /**
     * Save the given compilation unit to the given path.
     * @param cu the compilation unit
     * @param path the path of the java file
     * @param encoding  the encoding to use while saving the file
     */
    private SourceRoot save(CompilationUnit cu, Path path, Charset encoding) {
        assertNotNull(cu);
        assertNotNull(path);
        cu.setStorage(path, encoding);
        cu.getStorage().get().save(printer);
        return this;
    }

    /**
     * Save all previously parsed files back to a new path.
     * @param root the root of the java packages
     * @param encoding the encoding to use while saving the file
     */
    public SourceRoot saveAll(Path root, Charset encoding) {
        assertNotNull(root);
        Log.info("Saving all files (%s) to %s", cache::size, () -> root);
        for (Map.Entry<Path, ParseResult<CompilationUnit>> cu : cache.entrySet()) {
            final Path path = root.resolve(cu.getKey());
            if (cu.getValue().getResult().isPresent()) {
                Log.trace("Saving %s", () -> path);
                save(cu.getValue().getResult().get(), path, encoding);
            }
        }
        return this;
    }

    /**
     * Save all previously parsed files back to a new path.
     * @param root the root of the java packages
     */
    public SourceRoot saveAll(Path root) {
        return saveAll(root, parserConfiguration.getCharacterEncoding());
    }

    /**
     * Save all previously parsed files back to where they were found.
     */
    public SourceRoot saveAll() {
        return saveAll(root);
    }

    /**
     * Save all previously parsed files back to where they were found, with the given encoding.
     * @param encoding the encoding to use.
     */
    public SourceRoot saveAll(Charset encoding) {
        return saveAll(root, encoding);
    }

    /**
     * The Java files that have been parsed by this source root object, or have been added manually.
     */
    public List<ParseResult<CompilationUnit>> getCache() {
        return new ArrayList<>(cache.values());
    }

    /**
     * The CompilationUnits of the Java files that have been parsed succesfully by this source root object, or have been
     * added manually.
     */
    public List<CompilationUnit> getCompilationUnits() {
        return cache.values().stream()
                .filter(ParseResult::isSuccessful)
                .map(p -> p.getResult().get())
                .collect(Collectors.toList());
    }

    /**
     * The path that was passed in the constructor.
     */
    public Path getRoot() {
        return root;
    }

    public ParserConfiguration getParserConfiguration() {
        return parserConfiguration;
    }

    /**
     * Set the parser configuration that is used for parsing when no configuration is passed to a method.
     */
    public SourceRoot setParserConfiguration(ParserConfiguration parserConfiguration) {
        assertNotNull(parserConfiguration);
        this.parserConfiguration = parserConfiguration;
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

    /**
     * Get the printing function.
     */
    public Function<CompilationUnit, String> getPrinter() {
        return printer;
    }

    /**
     * Executes a recursive file tree walk using threads. A new thread is invoked for each new directory discovered
     * during the walk. For each file visited, the user-provided {@link VisitFileCallback} is called with the current
     * path and file attributes. Any shared resources accessed in a {@link VisitFileCallback} should be made
     * thread-safe.
     */
    private static class ParallelParse extends RecursiveAction {

        private static final long serialVersionUID = 1L;
        private final Path path;
        private final VisitFileCallback callback;

        ParallelParse(Path path, VisitFileCallback callback) {
            this.path = path;
            this.callback = callback;
        }

        @Override
        protected void compute() {
            final List<ParallelParse> walks = new ArrayList<>();
            try {
                Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
                    @Override
                    public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                        if (!SourceRoot.isSensibleDirectoryToEnter(dir)) {
                            return SKIP_SUBTREE;
                        }
                        if (!dir.equals(ParallelParse.this.path)) {
                            ParallelParse w = new ParallelParse(dir, callback);
                            w.fork();
                            walks.add(w);
                            return SKIP_SUBTREE;
                        } else {
                            return CONTINUE;
                        }
                    }

                    @Override
                    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                        return callback.process(file, attrs);
                    }
                });
            } catch (IOException e) {
                Log.error(e);
            }

            for (ParallelParse w : walks) {
                w.join();
            }
        }

        interface VisitFileCallback {
            FileVisitResult process(Path file, BasicFileAttributes attrs);
        }
    }

    @Override
    public String toString() {
        return "SourceRoot at " + root;
    }
}
