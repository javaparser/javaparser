package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import java.io.IOException;
import java.nio.file.Path;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class Issue4846Test extends AbstractResolutionTest {
    public static final Path SRC_DIR = adaptPath("src/test/resources/issue4846");

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new JavaParserTypeSolver(SRC_DIR))))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);

        javaParser = new JavaParser(configuration);
    }

    @Test
    void test() throws IOException {
        CompilationUnit cu = javaParser
                .parse(SRC_DIR.resolve("foo").resolve("Main.java"))
                .getResult()
                .get();
        TypeDeclaration<?> typeDec = cu.getType(0);
        MethodDeclaration methodDec = typeDec.getMethodsByName("foo").get(0);
        assertDoesNotThrow(methodDec::toDescriptor);
    }
}
