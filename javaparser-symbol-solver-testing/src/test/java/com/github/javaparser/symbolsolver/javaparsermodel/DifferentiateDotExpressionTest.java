package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class DifferentiateDotExpressionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath("src/test/resources/differentiate_dot_expressions"), new LeanParserConfiguration()));
        typeSolver = combinedTypeSolver;
    }

    @Test
    void methodCallsFromFieldObjects() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("FieldDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr firstFieldMethodCall = Navigator.findMethodCall(mainMethod, "firstContainerMethod").get();
        MethodCallExpr secondFieldMethodCall = Navigator.findMethodCall(mainMethod, "secondContainerMethod").get();
        MethodCallExpr thirdFieldMethodCall = Navigator.findMethodCall(mainMethod, "thirdContainerMethod").get();

        assertEquals(true, javaParserFacade.solve(firstFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(secondFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(thirdFieldMethodCall).isSolved());
    }

    @Test
    void staticMethodCallsFromInnerClasses() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("InnerClassDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr methodCall = Navigator.findMethodCall(mainMethod, "methodCall").get();
        MethodCallExpr innerMethodCall = Navigator.findMethodCall(mainMethod, "innerMethodCall").get();
        MethodCallExpr innerInnerMethodCall = Navigator.findMethodCall(mainMethod, "innerInnerMethodCall").get();

        assertEquals(true, javaParserFacade.solve(methodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerInnerMethodCall).isSolved());
    }

    @Test
    void staticFieldCallsFromInnerClasses() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("InnerStaticClassFieldDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr methodCallWithNestedStaticFieldParam = Navigator.findMethodCall(mainMethod, "parseInt").get();

        assertEquals(true, javaParserFacade.solve(methodCallWithNestedStaticFieldParam).isSolved());
    }

    @Test
    void packageStaticMethodCalls() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("PackageDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr staticMethodCall = Navigator.findMethodCall(mainMethod, "staticMethod").get();

        MethodCallExpr methodCall = Navigator.findMethodCall(mainMethod, "methodCall").get();
        MethodCallExpr innerMethodCall = Navigator.findMethodCall(mainMethod, "innerMethodCall").get();
        MethodCallExpr innerInnerMethodCall = Navigator.findMethodCall(mainMethod, "innerInnerMethodCall").get();

        MethodCallExpr firstFieldMethodCall = Navigator.findMethodCall(mainMethod, "firstContainerMethod").get();
        MethodCallExpr secondFieldMethodCall = Navigator.findMethodCall(mainMethod, "secondContainerMethod").get();
        MethodCallExpr thirdFieldMethodCall = Navigator.findMethodCall(mainMethod, "thirdContainerMethod").get();

        assertEquals(true, javaParserFacade.solve(staticMethodCall).isSolved());

        assertEquals(true, javaParserFacade.solve(methodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerInnerMethodCall).isSolved());

        assertEquals(true, javaParserFacade.solve(firstFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(secondFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(thirdFieldMethodCall).isSolved());
    }
}
