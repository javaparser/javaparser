package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

public class SolveMethodDeclaredInEnumTest extends AbstractTest {

    @Test
    public void methodDeclaredInEnum_enumFromJar() throws IOException {
        String code = "public class A { public void callEnum() { MyEnum.CONST.method(); }}";
        Path jarPath = adaptPath("src/test/resources/solveMethodDeclaredInEnum/MyEnum.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(jarPath), new ReflectionTypeSolver());

        ParserConfiguration parserConfiguration = new ParserConfiguration().setSymbolResolver(
                new JavaSymbolSolver(typeSolver));
        JavaParser javaParser = new JavaParser(parserConfiguration);

        CompilationUnit cu = javaParser.parse(ParseStart.COMPILATION_UNIT, new StringProvider(code)).getResult().get();

        MethodCallExpr call = cu.findFirst(MethodCallExpr.class).orElse(null);
        ResolvedMethodDeclaration resolvedCall = call.resolve();

        assertNotNull(resolvedCall);
        assertEquals("MyEnum.method()", resolvedCall.getQualifiedSignature());
    }

}
