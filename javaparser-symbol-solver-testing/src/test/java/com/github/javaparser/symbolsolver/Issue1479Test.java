package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue1479Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() throws IOException {
        
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(adaptPath("src/test/resources/issue1479")));
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);
        
        String src = 
                "public class Foo {\n" +
                "  public void m() {\n" +
                "    doSomething(B.AFIELD);\n" +
                "  }\n" +
                "  public void doSomething(String a) {\n" +
                "  }\n" +
                "}\n";

        CompilationUnit cu = StaticJavaParser.parse(src);
        FieldAccessExpr fae = cu.findFirst(FieldAccessExpr.class).get();
        assertTrue(fae.calculateResolvedType().describe().equals("java.lang.String"));
        ResolvedFieldDeclaration value = fae.resolve().asField();
        assertTrue(value.getName().equals("AFIELD"));
        Optional<FieldDeclaration> fd = value.toAst();
        assertEquals("a", fd.get().getVariable(0).getInitializer().get().asStringLiteralExpr().getValue());
    }
    
}
