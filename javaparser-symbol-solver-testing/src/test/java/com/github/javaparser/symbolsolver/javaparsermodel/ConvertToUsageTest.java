package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.*;

public class ConvertToUsageTest extends AbstractResolutionTest {

    TypeSolver typeSolver = new ReflectionTypeSolver();

    @Test
    public void testConvertTypeToUsage() {
        CompilationUnit cu = parseSample("LocalTypeDeclarations");
        List<NameExpr> n = cu.findAll(NameExpr.class);

        assertEquals("int", usageDescribe(n, "a"));
        assertEquals("java.lang.Integer", usageDescribe(n, "b"));
        assertEquals("java.lang.Class<java.lang.Integer>", usageDescribe(n, "c"));
        assertEquals("java.lang.Class<? super java.lang.Integer>", usageDescribe(n, "d"));
        assertEquals("java.lang.Class<? extends java.lang.Integer>", usageDescribe(n, "e"));
        assertEquals("java.lang.Class<? extends java.lang.Class<? super java.lang.Class<? extends java.lang.Integer>>>", usageDescribe(n, "f"));
        assertEquals("java.lang.Class<? super java.lang.Class<? extends java.lang.Class<? super java.lang.Integer>>>", usageDescribe(n, "g"));
    }

    private String usageDescribe(List<NameExpr> n, String name){
        return n.stream().filter(x -> x.getNameAsString().equals(name))
                .map(JavaParserFacade.get(typeSolver)::getType)
                .map(ResolvedType::describe)
                .findFirst().orElse(null);
    }
}
