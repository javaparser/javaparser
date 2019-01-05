package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertNotNull;


class Issue185 extends AbstractResolutionTest {

    @Test
    void testIssue() throws IOException {
        Path src = adaptPath("src/test/resources/recursion-issue");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        combinedTypeSolver.add(new ReflectionTypeSolver());
        CompilationUnit agendaCu = JavaParser.parse(adaptPath("src/test/resources/recursion-issue/Usage.java"));
        MethodCallExpr foo = Navigator.findMethodCall(agendaCu, "foo").get();
        assertNotNull(foo);
        JavaParserFacade.get(combinedTypeSolver).getType(foo);
    }

}
