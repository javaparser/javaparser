package com.github.javaparser.utils;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SourceRootTest {
    private final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/");
    private final SourceRoot sourceRoot = new SourceRoot(root);

    @BeforeEach
    void before() {
        sourceRoot.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
    }

    @Test
    void parseTestDirectory() throws IOException {

        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();
        List<CompilationUnit> units = sourceRoot.getCompilationUnits();

        assertEquals(2, units.size());
        assertTrue(units.stream().allMatch(unit -> !unit.getTypes().isEmpty() || unit.getModule().isPresent()));
        assertTrue(parseResults.stream().noneMatch(cu -> cu.getResult().get().getStorage().get().getPath().toString().contains("source.root")));
    }

    @Test
    void saveInCallback() throws IOException {
        sourceRoot.parse("", sourceRoot.getParserConfiguration(), (localPath, absolutePath, result) -> SourceRoot.Callback.Result.SAVE);
    }

    @Test
    void saveInCallbackParallelized() {
        sourceRoot.parseParallelized("", sourceRoot.getParserConfiguration(), ((localPath, absolutePath, result) ->
                SourceRoot.Callback.Result.SAVE));
    }

    @Test
    void fileAsRootIsNotAllowed() {
        assertThrows(IllegalArgumentException.class, () -> {
            Path path = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("com/github/javaparser/utils/Bla.java");
        new SourceRoot(path);
    });
}

    @Test
    void dotsInRootDirectoryAreAllowed() throws IOException {
        Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/source.root");
        new SourceRoot(path).tryToParse();
    }

    @Test
    void dotsInPackageAreNotAllowed() {
        assertThrows(ParseProblemException.class, () -> {
            Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils");
        new SourceRoot(path).parse("source.root", "Y.java");
    });
}
}
