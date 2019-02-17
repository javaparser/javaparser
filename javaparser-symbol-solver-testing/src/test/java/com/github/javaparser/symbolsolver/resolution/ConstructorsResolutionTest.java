package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserConstructorDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class ConstructorsResolutionTest extends AbstractResolutionTest {

    @AfterEach
    void resetConfiguration() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    @Test
    void solveNormalConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testNormalConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration otherClazz = Navigator.demandClass(cu, "OtherClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(otherClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveInnerClassConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerClassConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(1)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveInnerClassConstructorWithNewScope() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerClassConstructorWithNewScope");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveInnerInnerClassConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerInnerClassConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass.InnerInnerClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveEnumConstructor() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ConstructorCallsEnum");
        EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "ConstructorCallsEnum");
        ConstructorDeclaration constructor = (ConstructorDeclaration) enumDeclaration.getChildNodes().get(3);

        ResolvedConstructorDeclaration resolvedConstructor = constructor.resolve();

        assertEquals("ConstructorCallsEnum", resolvedConstructor.declaringType().getName());
        assertEquals(1, resolvedConstructor.getNumberOfParams());
        assertEquals("i", resolvedConstructor.getParam(0).getName());
        assertEquals(ResolvedPrimitiveType.INT, resolvedConstructor.getParam(0).getType());
    }

    @Test
    void solveNonPublicParentConstructorReflection() {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ReflectionTypeSolverConstructorResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ReflectionTypeSolverConstructionResolution");
        ConstructorDeclaration constructorDeclaration = Navigator.demandConstructor(clazz, 0);
        ExplicitConstructorInvocationStmt stmt =
                (ExplicitConstructorInvocationStmt) constructorDeclaration.getBody().getStatement(0);

        ResolvedConstructorDeclaration cd = stmt.resolve();

        assertEquals(1, cd.getNumberOfParams());
        assertEquals(ResolvedPrimitiveType.INT, cd.getParam(0).getType());
        assertEquals("java.lang.AbstractStringBuilder", cd.declaringType().getQualifiedName());
    }

}
