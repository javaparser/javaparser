package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue3173Test extends AbstractResolutionTest {

    @Test
    public void test() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String s =
                "public class Program {\n" +
                        "\n" +
                        "    public @interface AnnotationClass {\n" +
                        "    }\n" +
                        "}";

        CompilationUnit cu = StaticJavaParser.parse(s);
        List<AnnotationDeclaration> annDecls = cu.findAll(AnnotationDeclaration.class);
        annDecls.forEach(annDecl -> {
            assertTrue(annDecl.resolve().isAnnotation());
            assertEquals("AnnotationClass", annDecl.resolve().asAnnotation().getName());
        });
    }
}
