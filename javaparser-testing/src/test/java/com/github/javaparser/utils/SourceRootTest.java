package com.github.javaparser.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class SourceRootTest {
    @Test
    public void parseTestDirectory() throws URISyntaxException, IOException {
        SourceRoot sourceRoot = new SourceRoot(CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve(Paths.get("src", "test", "resources", "com", "github", "javaparser", "utils")));
        Map<Path, ParseResult<CompilationUnit>> results = sourceRoot.tryToParse();
        assertEquals(2, results.size());

        for (ParseResult<CompilationUnit> curesult : results.values()) {
            CompilationUnit cu = curesult.getResult().get();
            if(!(cu.getModule().isPresent() || !cu.getTypes().isEmpty())){
                fail();
            }
        }
    }
}
