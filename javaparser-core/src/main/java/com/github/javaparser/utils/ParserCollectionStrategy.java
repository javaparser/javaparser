package com.github.javaparser.utils;

import com.github.javaparser.ParserConfiguration;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;

import static java.nio.file.FileVisitResult.*;

/**
 * A brute force strategy for discovering a project structure.
 * It will search through the given project root path for Java files,
 * look at their package declarations, and figure out the root directories for those files.
 * No project definition files like pom.xml or build.gradle are used.
 * This strategy is crude, but can work for many cases.
 * Note that any build artifacts will also be detected: jar files in target directories and so on.
 */
public class ParserCollectionStrategy implements CollectionStrategy {

    private final ParserConfiguration parserConfiguration;

    public ParserCollectionStrategy() {
        this(new ParserConfiguration());
    }

    public ParserCollectionStrategy(ParserConfiguration parserConfiguration) {
        this.parserConfiguration = parserConfiguration;
    }

    @Override
    public ProjectRoot collect(Path path) {
        ProjectRoot projectRoot = new ProjectRoot(path, parserConfiguration);
        try {
            Files.walkFileTree(path, new SimpleFileVisitor<Path>() {
                private Path currentRoot;
                private PathMatcher javaMatcher = getPathMatcher("glob:**.java");
                private PathMatcher jarMatcher = getPathMatcher("glob:**.jar");

                @Override
                public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                    if (javaMatcher.matches(file)) {
                        currentRoot = getRoot(file).orElse(null);
                        if (currentRoot != null) {
                            return SKIP_SIBLINGS;
                        }
                    } else if (jarMatcher.matches(file)) {
                        projectRoot.addJarFile(file);
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                    if (Files.isHidden(dir) || (currentRoot != null && dir.startsWith(currentRoot))) {
                        return SKIP_SUBTREE;
                    }
                    return CONTINUE;
                }

                @Override
                public FileVisitResult postVisitDirectory(Path dir, IOException e) {
                    if (dir.equals(currentRoot)) {
                        projectRoot.addSourceRoot(dir);
                        currentRoot = null;
                    }
                    return CONTINUE;
                }
            });
        } catch (IOException e) {
            Log.error(e, "Unable to walk %s", path);
        }
        return projectRoot;
    }
}
