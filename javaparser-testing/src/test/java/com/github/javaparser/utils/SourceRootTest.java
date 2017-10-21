package com.github.javaparser.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


public class SourceRootTest {
    private final Path root = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("com/github/javaparser/utils/");
    private final SourceRoot sourceRoot = new SourceRoot(root);

    @Test
    public void parseTestDirectory() throws URISyntaxException, IOException {

        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();
        List<CompilationUnit> units = sourceRoot.getCompilationUnits();

        assertEquals(2, units.size());
        assertEquals(true, units.stream().allMatch(unit -> !unit.getTypes().isEmpty() || unit.getModule().isPresent()));
        assertEquals(true, parseResults.stream().anyMatch(cu -> cu.getResult().get().getStorage().get().getPath().toString().contains("source" + File.separator + "root")));
    }

    @Test
    public void fileAsRootIsNotAllowed() {
        Path path = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("/com/github/javaparser/utils/Bla.java");
        assertThrows(IllegalArgumentException.class,() -> new SourceRoot(path));
    }
    
    

}
