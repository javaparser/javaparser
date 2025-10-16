package com.github.javaparser.utils;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SourceRootPathResolutionTest {

    private static Path N(Path p) {
        return p.toAbsolutePath().normalize();
    }

    @Test
    void relative_is_resolved_under_newRoot_pathResolveBehaviour() throws Exception {
        Path oldRoot = Files.createTempDirectory("jp-old-");
        Path newRoot = Files.createTempDirectory("jp-new-");
        SourceRoot sr = new SourceRoot(oldRoot);

        Path relKey = Paths.get("pkg/A.java");
        Path got = sr.resolveSavePath(newRoot, relKey);

        assertEquals(N(newRoot.resolve(relKey)), N(got));
    }

    @Test
    void absolute_is_returned_unchanged_pathResolveBehaviour() throws Exception {
        Path oldRoot = Files.createTempDirectory("jp-old-");
        Path newRoot = Files.createTempDirectory("jp-new-");
        SourceRoot sr = new SourceRoot(oldRoot);

        Path absKey = oldRoot.resolve("pkg/B.java").toAbsolutePath();
        Path got = sr.resolveSavePath(newRoot, absKey);

        assertEquals(N(absKey), N(got));
    }

    @Test
    void saveAll_uses_resolution_for_relative_and_absolute_keys() throws Exception {
        Path oldRoot = Files.createTempDirectory("jp-old-");
        Path newRoot = Files.createTempDirectory("jp-new-");
        SourceRoot sr = new SourceRoot(oldRoot);


        CompilationUnit cuRel = new CompilationUnit();
        sr.add("pkg", "Rel.java", cuRel);
        Path expectedRelTarget = N(newRoot.resolve("pkg/Rel.java"));
        assertEquals(expectedRelTarget, N(sr.resolveSavePath(newRoot, Paths.get("pkg/Rel.java"))));


        Path absKey = oldRoot.resolve("pkg/Abs.java").toAbsolutePath();
        Files.createDirectories(absKey.getParent());
        CompilationUnit cuAbs = new CompilationUnit();
        cuAbs.setStorage(absKey, StandardCharsets.UTF_8);
        sr.add(cuAbs);
        Path expectedAbsTarget = N(absKey);
        assertEquals(expectedAbsTarget, N(sr.resolveSavePath(newRoot, absKey)));
    }
}
