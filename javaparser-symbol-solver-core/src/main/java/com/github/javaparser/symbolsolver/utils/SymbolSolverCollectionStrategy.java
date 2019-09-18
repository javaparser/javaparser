package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CollectionStrategy;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.ProjectRoot;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;

import static java.nio.file.FileVisitResult.CONTINUE;
import static java.nio.file.FileVisitResult.SKIP_SUBTREE;

/**
 * {@link CollectionStrategy} which collects all SourceRoots and initialises the TypeSolver and returns the SourceRoots configured
 * with the TypeSolver in a ProjectRoot object.
 */
public class SymbolSolverCollectionStrategy implements CollectionStrategy {

    private final ParserConfiguration parserConfiguration;
    private final CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));

    public SymbolSolverCollectionStrategy() {
        this(new ParserConfiguration());
    }

    public SymbolSolverCollectionStrategy(ParserConfiguration parserConfiguration) {
        this.parserConfiguration = parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @Override
    public ProjectRoot collect(Path path) {
        ProjectRoot projectRoot = new ProjectRoot(path, parserConfiguration);
        try {
            Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
                private Path current_root;
                private PathMatcher javaMatcher = getPathMatcher("glob:**.java");
                private PathMatcher jarMatcher = getPathMatcher("glob:**.jar");

                @Override
                public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                    if (javaMatcher.matches(file)) {
                        if (current_root == null || !file.startsWith(current_root)) {
                            current_root = getRoot(file).orElse(null);
                        }
                    } else if (jarMatcher.matches(file)) {
                        typeSolver.add(new JarTypeSolver(file.toString()));
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                    if (Files.isHidden(dir)) {
                        return SKIP_SUBTREE;
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult postVisitDirectory(Path dir, IOException e) throws IOException {
                    if (current_root != null && Files.isSameFile(dir, current_root)) {
                        projectRoot.addSourceRoot(dir);
                        typeSolver.add(new JavaParserTypeSolver(current_root.toFile()));
                        current_root = null;
                    }
                    return CONTINUE;
                }
            });
        } catch (IOException e) {
            Log.error(e, "Unable to walk %s", () -> path);
        }
        return projectRoot;
    }
}
