package com.github.javaparser.utils;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class SourceRootTest {
    private final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/");
    private final SourceRoot sourceRoot = new SourceRoot(root);

    @Before
    public void before() {
        sourceRoot.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
    }

    @Test
    public void parseTestDirectory() throws IOException {

        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();
        List<CompilationUnit> units = sourceRoot.getCompilationUnits();

        assertEquals(2, units.size());
        assertTrue(units.stream().allMatch(unit -> !unit.getTypes().isEmpty() || unit.getModule().isPresent()));
        assertTrue(parseResults.stream().noneMatch(cu -> cu.getResult().get().getStorage().get().getPath().toString().contains("source.root")));
    }

    @Test
    public void saveInCallback() throws IOException {
        sourceRoot.parse("", sourceRoot.getParserConfiguration(), (localPath, absolutePath, result) -> SourceRoot.Callback.Result.SAVE);
    }

    @Test
    public void saveInCallbackParallelized() {
        sourceRoot.parseParallelized("", sourceRoot.getParserConfiguration(), ((localPath, absolutePath, result) ->
                SourceRoot.Callback.Result.SAVE));
    }

    @Test(expected = IllegalArgumentException.class)
    public void fileAsRootIsNotAllowed() {
        Path path = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("com/github/javaparser/utils/Bla.java");
        new SourceRoot(path);
    }

    @Test
    public void dotsInRootDirectoryAreAllowed() throws IOException {
        Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/source.root");
        new SourceRoot(path).tryToParse();
    }

    @Test(expected = ParseProblemException.class)
    public void dotsInPackageAreNotAllowed() {
        Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils");
        new SourceRoot(path).parse("source.root", "Y.java");
    }
}
