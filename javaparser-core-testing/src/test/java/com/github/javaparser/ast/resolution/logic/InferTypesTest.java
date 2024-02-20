package com.github.javaparser.ast.resolution.logic;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class InferTypesTest extends MethodResolutionLogic {
    protected JavaParser createParserWithResolver(TypeSolver typeSolver) {
        return new JavaParser(new ParserConfiguration().setSymbolResolver(symbolResolver(typeSolver)));
    }

    protected SymbolResolver symbolResolver(TypeSolver typeSolver) {
        return new JavaSymbolSolver(typeSolver);
    }

    private ResolvedType getRefType() {
        String code = "public class Program {\n" +
                "\n" +
                "    public static class InnerClass<T> {\n" +
                "       void method1() {\n" +
                "           new InnerClass<T>();\n" + // Buggy
                "       }\n" +
                "       <T1> void method2() {\n" +
                "           new InnerClass<T1>();\n" + // OK
                "           new InnerClass<T>();\n" + // Buggy
                "       }\n" +
                "    }\n" +
                "}";

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(new ReflectionTypeSolver())).parse(code);
        List<ObjectCreationExpr> objCrtExprs = cu.findAll(ObjectCreationExpr.class);
        ObjectCreationExpr expr = objCrtExprs.get(0);
        ResolvedType resRefType = expr.getType().resolve();
        assertTrue(resRefType.isReferenceType());
        return resRefType;
    }

    @Test
    public void testPrimitive() {
        ResolvedType src = ResolvedPrimitiveType.BOOLEAN;
        ResolvedType tgt = ResolvedPrimitiveType.INT;
        Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings = new HashMap<ResolvedTypeParameterDeclaration, ResolvedType>();

        inferTypes(src, tgt, mappings);
        assertTrue(mappings.size() == 0);
    }

    @Test
    public void testSame(){
        ResolvedType t = getRefType();
        Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings = new HashMap<ResolvedTypeParameterDeclaration, ResolvedType>();

        inferTypes(t, t, mappings);
        assertTrue(mappings.size() == 0);
    }

    @Test
    public void testTypeVariableReference(){
        ResolvedType rt = getRefType();
        ResolvedTypeVariable rtv = new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList()));
        Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings = new HashMap<ResolvedTypeParameterDeclaration, ResolvedType>();

        inferTypes(rt, rtv, mappings);
        assertTrue(mappings.size() == 1);
    }

    @Test
    public void testTypeVariable(){
        ResolvedTypeVariable rtv = new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList()));
        ResolvedTypeVariable rtv2 = new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("B", "foo.Bar", Collections.emptyList()));
        Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings = new HashMap<ResolvedTypeParameterDeclaration, ResolvedType>();

        inferTypes(rtv, rtv2, mappings);
        assertTrue(mappings.size() == 1);
    }

}
