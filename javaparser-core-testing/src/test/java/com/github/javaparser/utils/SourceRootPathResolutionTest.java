package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SourceRootPathResolutionTest {

    private static Path N(Path p) { return p.toAbsolutePath().normalize(); }

    @Test
    void relative_is_resolved_under_newRoot_currentBehaviour() throws IOException {

        Path srcRoot = Files.createTempDirectory("jp-src-");
        Path newRoot = Files.createTempDirectory("jp-out-");

        SourceRoot sr = new SourceRoot(srcRoot);

        Path key = Paths.get("pkg").resolve("A.java");

        Path got = sr.resolveSavePath(newRoot, key);

        assertEquals(N(newRoot.resolve(key)), N(got));
    }

    @Test
    void absolute_is_returned_as_is_currentBehaviour() throws IOException {
        Path srcRoot = Files.createTempDirectory("jp-src-");
        Path newRoot = Files.createTempDirectory("jp-out-");

        SourceRoot sr = new SourceRoot(srcRoot);


        Path absDir = Files.createTempDirectory("jp-abs-");
        Path key = absDir.resolve("X.java").toAbsolutePath();

        Path got = sr.resolveSavePath(newRoot, key);

        assertEquals(N(key), N(got));
    }
}
