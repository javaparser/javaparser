package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistEnumDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue2953Test {
    @Test
    public void testResolveMethodOfEnumInheritedFromInterface() throws IOException {
        CombinedTypeSolver typeResolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));
        typeResolver.add(new JarTypeSolver("src/test/resources/issue2953/a.jar"));

        JavassistEnumDeclaration enumA = (JavassistEnumDeclaration) typeResolver.solveType("foo.A");
        SymbolReference<ResolvedMethodDeclaration> method = enumA
                .solveMethod("equalByCode", Arrays.asList(ResolvedPrimitiveType.INT), false);
        assertTrue(method.isSolved());
    }


    @Test
    public void testIssue2953() throws IOException {
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver typeResolver = new CombinedTypeSolver(new ReflectionTypeSolver(false));
        typeResolver.add(new JarTypeSolver("src/test/resources/issue2953/a.jar"));
        config.setSymbolResolver(new JavaSymbolSolver(typeResolver));
        StaticJavaParser.setConfiguration(config);

        String code = "package foo;\n"
                + "import foo.A;\n"
                + "public class Test {\n"
                + "    public void foo() {\n"
                + "        A.X.equalByCode(0);\n"
                + "    }\n"
                + "}";
        CompilationUnit cu = StaticJavaParser.parse(code);

        for (TypeDeclaration<?> type : cu.getTypes()) {
            type.ifClassOrInterfaceDeclaration(classDecl -> {
                for (MethodDeclaration method : classDecl.getMethods()) {
                    method.getBody().ifPresent(body -> {
                        for (Statement stmt : body.getStatements()) {
                            for (MethodCallExpr methodCallExpr : stmt.findAll(MethodCallExpr.class)) {
                                ResolvedMethodDeclaration resolvedMethodCall = methodCallExpr.resolve();
                                String methodSig = resolvedMethodCall.getQualifiedSignature();
                                assertEquals("foo.IB.equalByCode(java.lang.Integer)", methodSig);
                            }
                        }
                    });
                }
            });
        }
    }
}
