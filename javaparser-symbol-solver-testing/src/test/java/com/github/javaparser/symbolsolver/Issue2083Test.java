package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;


public class Issue2083Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {
        
        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "import static Simple.SPACES;\n" + 
                "public class Simple {\n" + 
                "  public enum IndentType {\n" + 
                "    SPACES\n" + 
                "  }\n" + 
                "  public IndentType c = SPACES;\n" + 
                "}";
        CompilationUnit cu = StaticJavaParser.parse(s);
        FieldDeclaration  fd = cu.findFirst(FieldDeclaration.class).get();
        assertEquals("Simple.IndentType", fd.resolve().getType().describe());
        
    }

}
