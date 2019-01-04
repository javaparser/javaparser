package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;


class ParserCollectionStrategyTest {

    private final Path root = CodeGenerationUtils.mavenModuleRoot(ParserCollectionStrategyTest.class).resolve("").getParent();
    private final ProjectRoot projectRoot = new ParserCollectionStrategy().collect(root);

    @Test
    void getSourceRoots() {
        assertFalse(projectRoot.getSourceRoots().size() == 0);
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve("javaparser-core/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-core-generators/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-core-metamodel-generator/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-symbol-solver-core/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-symbol-solver-logic/src/main/java")));
        assertNotEquals(Optional.empty(), projectRoot.getSourceRoot(root.resolve
                ("javaparser-symbol-solver-model/src/main/java")));
    }
}
