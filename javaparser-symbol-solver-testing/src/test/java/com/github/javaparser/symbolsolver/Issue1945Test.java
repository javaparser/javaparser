package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue1945Test extends AbstractResolutionTest {

    @Test()
    void test() {
        String code = "import issue1945.implementations.Sheep;\n" + 
                "import issue1945.interfaces.HairType;\n" + 
                "import issue1945.interfaces.HairTypeRenderer;\n" + 
                "import issue1945.interfaces.HairyAnimal;\n" + 
                "\n" + 
                "public class MainIssue1945 {\n" + 
                "    \n" + 
                "    private final HairyAnimal sheep = new Sheep();\n" + 
                "    \n" + 
                "    public void chokes3() {\n" + 
                "        HairType<?> hairType = sheep.getHairType();\n" + 
                "        hairType.getRenderer().renderHair(sheep.getHairType(), sheep);\n" + 
"        hairType.getRenderer();\n" + 
                
                "    }\n" + 
                "    \n" + 
                "    public void chokes() {\n" + 
                "        sheep.getHairType().getRenderer().renderHair(sheep.getHairType(), sheep);\n" +
                "    }\n" + 
                "    \n" + 
                "    public void chokes2() {\n" + 
                "        HairType<?> hairType = sheep.getHairType();\n" + 
                "        hairType.getRenderer().renderHair(hairType, sheep);\n" + 
                "    }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        Path srcDir = adaptPath("src/test/resources/issue1945");
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(false), new JavaParserTypeSolver(srcDir));
        
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);
        
        // results by MathodCallExpr
        Map<String,String> resultsQualifiedName = new HashMap<>();
        resultsQualifiedName.put("sheep.getHairType()", "issue1945.interfaces.HairyAnimal.getHairType");
        resultsQualifiedName.put("hairType.getRenderer().renderHair(sheep.getHairType(), sheep)", "issue1945.interfaces.HairTypeRenderer.renderHair");
        resultsQualifiedName.put("hairType.getRenderer()", "issue1945.interfaces.HairType.getRenderer");
        resultsQualifiedName.put("sheep.getHairType().getRenderer().renderHair(sheep.getHairType(), sheep)", "issue1945.interfaces.HairTypeRenderer.renderHair");
        resultsQualifiedName.put("sheep.getHairType().getRenderer()", "issue1945.interfaces.HairType.getRenderer");
        resultsQualifiedName.put("hairType.getRenderer().renderHair(hairType, sheep)", "issue1945.interfaces.HairTypeRenderer.renderHair");
        Map<String,String> resultsResolvedType = new HashMap<>();
        resultsResolvedType.put("sheep.getHairType()", "issue1945.interfaces.HairType<?>");
        resultsResolvedType.put("hairType.getRenderer().renderHair(sheep.getHairType(), sheep)", "void");
        resultsResolvedType.put("hairType.getRenderer()", "R");
        resultsResolvedType.put("sheep.getHairType().getRenderer().renderHair(sheep.getHairType(), sheep)", "void");
        resultsResolvedType.put("sheep.getHairType().getRenderer()", "R");
        resultsResolvedType.put("hairType.getRenderer().renderHair(hairType, sheep)", "void");

        CompilationUnit cu = StaticJavaParser.parse(code);
        List<MethodCallExpr> nodes = cu.findAll(MethodCallExpr.class);
        for (MethodCallExpr expr : nodes) {
            String qName = expr.resolve().getQualifiedName();
            String resolvedType = expr.calculateResolvedType().describe();
            assertEquals(resultsQualifiedName.get(expr.toString()), qName);
            assertEquals(resultsResolvedType.get(expr.toString()), resolvedType);
        }
        
    }

}
