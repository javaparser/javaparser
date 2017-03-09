package com.github.javaparser.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class SourceRootTest {

    @Test
    public void parseTestDirectory() throws URISyntaxException, IOException {
        Path root = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("com/github/javaparser/utils/");
        SourceRoot sourceRoot = new SourceRoot(root);

        Map<Path, ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();
        List<CompilationUnit> units = sourceRoot.getCompilationUnits();

        assertEquals(3, units.size());
        assertTrue(units.stream().allMatch(unit -> !unit.getTypes().isEmpty() || unit.getModule().isPresent()));
        assertTrue(parseResults.keySet().stream().anyMatch(path -> path.toString().contains("source" + File.separator + "root")));
    }

    @Test(expected = IllegalArgumentException.class)
    public void fileAsRootIsNotAllowed() {
        Path path = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("/com/github/javaparser/utils/Bla.java");
        new SourceRoot(path);
    }

}
