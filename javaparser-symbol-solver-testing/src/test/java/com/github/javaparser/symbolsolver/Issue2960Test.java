package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

public class Issue2960Test {
    @Test
    public void testIssue2960() {
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver typeResolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));
        typeResolver.add(new JavaParserTypeSolver("src/test/resources/issue2960"));
        config.setSymbolResolver(new JavaSymbolSolver(typeResolver));
        StaticJavaParser.setConfiguration(config);

        String code = "package foo;\n"
                + "import foo.A;\n"
                + "import foo.B;\n"
                + "public class Test {\n"
                + "    public void foo() {\n"
                + "        A a = new A();\n"
                + "        B b = new B();\n"
                + "        a.aLong(b.bExtendsNumber());\n"
                + "        a.aString(b.bExtendsNumber());\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodCallExpr aLongMethodCall = Navigator.findMethodCall(cu, "aLong").get();
        assertDoesNotThrow(aLongMethodCall::resolve);

        MethodCallExpr aStringMethodCall = Navigator.findMethodCall(cu, "aString").get();
        assertThrows(UnsolvedSymbolException.class, aStringMethodCall::resolve);
    }
}
