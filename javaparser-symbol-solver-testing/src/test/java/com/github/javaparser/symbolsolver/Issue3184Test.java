package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.utils.Pair;

public class Issue3184Test extends AbstractResolutionTest {

    @Test
    void test() {
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

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(code);
        List<ObjectCreationExpr> objCrtExprs = cu.findAll(ObjectCreationExpr.class);
        objCrtExprs.forEach(expr -> {
            ResolvedType resRefType = expr.getType().resolve();
            ResolvedReferenceTypeDeclaration resRefTypeDecl = resRefType.asReferenceType().getTypeDeclaration().get();
            List<ResolvedTypeParameterDeclaration> resTypeParamsDecl = resRefTypeDecl.getTypeParameters();
            List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> resTypeParamsDeclMap = resRefType.asReferenceType().getTypeParametersMap();
            assertFalse(resTypeParamsDecl.isEmpty());
            assertFalse(resTypeParamsDeclMap.isEmpty());
            for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> resTypeParamsDeclPair : resTypeParamsDeclMap) {
                assertTrue(resTypeParamsDeclPair.b.isTypeVariable());
            }
        });
    }
}
