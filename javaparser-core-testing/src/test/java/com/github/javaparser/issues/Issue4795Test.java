package com.github.javaparser.issues;

import java.nio.charset.StandardCharsets;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Issue #4795: SourceRoot.saveAll(Path) should respect the provided new root
 * even when a CompilationUnit has an absolute storage path.
 */
class Issue4795Test {

    @Test
    void absolutePathCuShouldBeSavedUnderNewRoot() throws IOException {
        Path tmp = Files.createTempDirectory("jp4795");
        Path oldProjectRoot = tmp.resolve("proj");
        Path oldSrc = oldProjectRoot.resolve("src/main/java/p");
        Files.createDirectories(oldSrc);

        Path oldFile = oldSrc.resolve("A.java");
        Files.write(oldFile, "package p; class A{}".getBytes(StandardCharsets.UTF_8));

        // Build SourceRoot on the old root and parse the file (this sets storage)
        SourceRoot sr = new SourceRoot(oldProjectRoot);
        ParseResult<CompilationUnit> pr = sr.tryToParse("src/main/java/p", "A.java");
        assertTrue(pr.isSuccessful(), "Parsing seed file should succeed");

        // Save to a new root
        Path newRoot = tmp.resolve("out");
        sr.saveAll(newRoot);

        Path expected = newRoot.resolve("src/main/java/p/A.java");
        assertTrue(Files.exists(expected),
                "A.java should be written under the provided new root: " + expected);
        // Original should remain
        assertTrue(Files.exists(oldFile), "Original file should remain untouched");
    }



}
