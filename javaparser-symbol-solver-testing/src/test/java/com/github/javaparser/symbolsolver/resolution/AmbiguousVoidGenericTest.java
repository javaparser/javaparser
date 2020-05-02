package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


/**
 * Unambigous ambiguity call with <Void> generics and lambda's
 * @see <a href="https://github.com/javaparser/javaparser/issues/1950">https://github.com/javaparser/javaparser/issues/1950</a>
 */
public class AmbiguousVoidGenericTest {

    @OpenIssueTest(issueNumber = {1950}, testcasePrNumber = 1958)
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
