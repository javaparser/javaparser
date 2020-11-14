package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue2284Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {

        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "public enum Enum {\n" + 
                "    CONSTANT_ENUM() {\n" + 
                "        @Override\n" + 
                "        String getEnumName() {\n" + 
                "            return \"CONSTANT_ENUM\";\n" + 
                "        }\n" + 
                "    };\n" + 
                "  \n" + 
                "    String getEnumName() {\n" + 
                "        return \"default\";\n" + 
                "    }\n" + 
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<MethodDeclaration> mds = cu.findAll(MethodDeclaration.class);
        mds.forEach(md-> {
            assertEquals("Enum.getEnumName()", md.resolve().getQualifiedSignature());
        });

    }
    
}
