package com.github.javaparser.utils;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SourceRootPathResolutionTest {

    @Test
    void relativeKey_resolvesUnderNewRoot() {
        Path newRoot = Paths.get("/out");
        Path oldRoot = Paths.get("/proj");
        Path key = Paths.get("src/main/java/p/A.java");

        Path result = SourceRoot.resolveSavePath(newRoot, oldRoot, key, Optional.empty());
        assertEquals(Paths.get("/out/src/main/java/p/A.java"), result);
    }

    @Test
    void absoluteUnderOldRoot_isRelativizedThenReRooted() {
        Path newRoot = Paths.get("/out");
        Path oldRoot = Paths.get("/proj");
        Path key = Paths.get("/proj/src/main/java/p/A.java");

        Path result = SourceRoot.resolveSavePath(newRoot, oldRoot, key, Optional.empty());
        assertEquals(Paths.get("/out/src/main/java/p/A.java"), result);
    }

    @Test
    void absoluteOutsideOldRoot_usesPackageAndPrimaryType() {
        Path newRoot = Paths.get("/out");
        Path oldRoot = Paths.get("/proj");
        Path key = Paths.get("/somewhere/else/X.java");

        CompilationUnit cu = StaticJavaParser.parse("package p.q; public class A {}");
        Path result = SourceRoot.resolveSavePath(newRoot, oldRoot, key, Optional.of(cu));

        assertEquals(Paths.get("/out/src/main/java/p/q/A.java"), result);
    }

    @Test
    void absoluteOutsideOldRoot_withoutCu_usesFilename() {
        Path newRoot = Paths.get("/out");
        Path oldRoot = Paths.get("/proj");
        Path key = Paths.get("/somewhere/else/X.java");

        Path result = SourceRoot.resolveSavePath(newRoot, oldRoot, key, Optional.empty());
        assertEquals(Paths.get("/out/src/main/java/X.java"), result);
    }
}
