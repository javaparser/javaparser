package com.github.javaparser.symbolsolver.resolution;

import static org.junit.Assert.*;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class AmbiguousVoidGenericTest {

    @Test
    public void issueWithInternalEnumConstantReference() {
        String code = "package com.github.javaparser.symbolsolver.testingclasses; class Foo { void foo() { UtilityClass.method(()->{}); } }";
        JavaParser jp = new JavaParser();
        jp.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));

        ParseResult<CompilationUnit> pr = jp.parse(ParseStart.COMPILATION_UNIT, new StringProvider(code));
        assertTrue(pr.isSuccessful());

        MethodCallExpr methodCallExpr = pr.getResult().get().findFirst(MethodCallExpr.class).get();
        ResolvedMethodDeclaration resolved = methodCallExpr.resolve();

        assertEquals("Incorrect ambiguity resolution", resolved.getParam(0).getType().describe(),
                Runnable.class.getName());
    }

}
