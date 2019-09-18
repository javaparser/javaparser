package com.github.javaparser.utils;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ast.CompilationUnit;

import java.io.FileNotFoundException;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.Optional;

import static com.github.javaparser.StaticJavaParser.parse;

/**
 * A strategy for discovering the structure of a project.
 * Implementations could read a pom.xml, a Gradle build file, a makefile...
 */
public interface CollectionStrategy {

    ProjectRoot collect(Path path);

    default Optional<Path> getRoot(Path file) throws FileNotFoundException {
        try {
            return parse(file.toFile()).getStorage()
                    .map(CompilationUnit.Storage::getSourceRoot);
        } catch (ParseProblemException e) {
            Log.info("Problem parsing file %s", () -> file);
        } catch (RuntimeException e) {
            Log.info("Could not parse file %s", () -> file);
        }
        return Optional.empty();
    }

    default PathMatcher getPathMatcher(String pattern) {
        return FileSystems.getDefault().getPathMatcher(pattern);
    }
}
