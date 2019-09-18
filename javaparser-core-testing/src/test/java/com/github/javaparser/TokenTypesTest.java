package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.SwitchEntry;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.utils.CodeGenerationUtils.mavenModuleRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class TokenTypesTest {
    @Test
    void everyTokenHasACategory() throws IOException {
        final int tokenCount = GeneratedJavaParserConstants.tokenImage.length;
        Path tokenTypesPath = mavenModuleRoot(JavaParserTest.class).resolve("../javaparser-core/src/main/java/com/github/javaparser/TokenTypes.java");
        CompilationUnit tokenTypesCu = parse(tokenTypesPath);
        // -1 to take off the default: case.
        int switchEntries = tokenTypesCu.findAll(SwitchEntry.class).size() - 1;
        // The amount of "case XXX:" in TokenTypes.java should be equal to the amount of tokens JavaCC knows about:
        assertEquals(tokenCount, switchEntries);
    }
}
