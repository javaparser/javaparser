package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class Issue251Test extends AbstractResolutionTest{

    @Test
    void testSolveStaticallyImportedMemberType() {
        CompilationUnit cu = parseSample("Issue251");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "Main");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodDeclaration m = Navigator.demandMethod(cls, "bar");
        ExpressionStmt stmt = (ExpressionStmt) m.getBody().get().getStatements().get(1);
        MethodCallExpr expression = (MethodCallExpr) stmt.getExpression();
        Assertions.assertNotNull(javaParserFacade.solve(expression));
    }
}
