package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class Issue1946 {


    @Test
    public void issueWithInternalEnumConstantReference() {
        String code = "package com.github.javaparser.symbolsolver.testingclasses; class Foo { void foo() { UtilityClass.method(SomeClass.InnerEnum.CONSTANT); } }";
        JavaParser jp = new JavaParser();
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(new TypeSolver[] {
                new ReflectionTypeSolver(false)
        });
        jp.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        ParseResult<CompilationUnit> pr = jp.parse(ParseStart.COMPILATION_UNIT, new StringProvider(code));
        assertEquals(true, pr.isSuccessful());
        MethodCallExpr methodCallExpr = pr.getResult().get().findFirst(MethodCallExpr.class).get();
        methodCallExpr.resolve();
    }
}
