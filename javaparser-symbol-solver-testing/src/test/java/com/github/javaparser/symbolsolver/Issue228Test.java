package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue228Test extends AbstractResolutionTest{

    @Test
    void testSolvingMethodWitPrimitiveParameterTypeAsUsage() {
        String code = 
                  "class Test { "
                + "  long l = call(1); "
                + "  long call(final long i) { "
                + "    return i; "
                + "  }"
                + "}";
        CompilationUnit cu = parse(code);
        MethodCallExpr methodCall = cu.findAll(MethodCallExpr.class).get(0);
        JavaParserFacade parserFacade = JavaParserFacade.get(new ReflectionTypeSolver());
        MethodUsage solvedCall = parserFacade.solveMethodAsUsage(methodCall);
        assertEquals("long", solvedCall.getParamType(0).describe());
    }
}
