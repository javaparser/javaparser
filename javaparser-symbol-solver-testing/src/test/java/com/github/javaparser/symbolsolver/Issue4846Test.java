package com.github.javaparser.symbolsolver;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.*;
import org.junit.jupiter.api.*;

import java.io.IOException;
import java.nio.file.Path;
import java.sql.Ref;

public class Issue4846Test extends AbstractResolutionTest {
    public static final Path SRC_DIR = adaptPath("src/test/resources/issue4846");

    private JavaParser javaParser;

    @BeforeEach
    void setup() {
        // clear internal caches
        JavaParserFacade.clearInstances();

        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(
                        new JavaParserTypeSolver(SRC_DIR)
                )))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16);

        javaParser = new JavaParser(configuration);
    }

    @Test
    void test() throws IOException {
        CompilationUnit cu = javaParser.parse(SRC_DIR.resolve("foo").resolve("Main.java")).getResult().get();
        TypeDeclaration<?> typeDec = cu.getType(0);
        MethodDeclaration methodDec = typeDec.getMethodsByName("foo").get(0);
        methodDec.toDescriptor();
    }
}
