package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue1774Test extends AbstractResolutionTest {

    @Test
    public void test() {
        StaticJavaParser.setConfiguration(new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false))));

        String str = 
                  "public class A { "
                + "  String s1 = false + \"str\";"
                + "  String s2 = 'a' + \"str\";"
                + "  String s3 = 1 + \"foo\";"
                + "  float f = 3 % 2.71f;"
                + "  double d = 3 % 2.0;"
                + "  Integer i1 = 'G' & 6;"
                + "  long l1 = 'z' & 1L;"
                + "  long l2 = 0x01 & 2L;"
                + "  Integer i2 = 'G' & 6;"
                + "  long l3 = 'z' & 1L;"
                + "  long l4 = 0x01 & 2L;"
                + "  int i10 = 'B' << 1;"
                + "  byte b = 8;"
                + "  int i11 = b >> 2;"
                + "  short s = 0x0f;"
                + "  int i12 = 'B' << 1;"
                + "}";
        CompilationUnit cu = StaticJavaParser.parse(str);
        List<BinaryExpr> exprs = cu.findAll(BinaryExpr.class);
        assertEquals("java.lang.String", exprs.get(0).calculateResolvedType().describe());
        assertEquals("java.lang.String", exprs.get(1).calculateResolvedType().describe());
        assertEquals("java.lang.String", exprs.get(2).calculateResolvedType().describe());
        assertEquals("float", exprs.get(3).calculateResolvedType().describe());
        assertEquals("double", exprs.get(4).calculateResolvedType().describe());
        assertEquals("int", exprs.get(5).calculateResolvedType().describe());
        assertEquals("long", exprs.get(6).calculateResolvedType().describe());
        assertEquals("long", exprs.get(7).calculateResolvedType().describe());
        assertEquals("int", exprs.get(8).calculateResolvedType().describe());
        assertEquals("long", exprs.get(9).calculateResolvedType().describe());
        assertEquals("long", exprs.get(10).calculateResolvedType().describe());
        
        // unary primitve promotion
        assertEquals("int", exprs.get(11).calculateResolvedType().describe());
        assertEquals("int", exprs.get(12).calculateResolvedType().describe());
        assertEquals("int", exprs.get(13).calculateResolvedType().describe());
        
    }

}
