package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Assert;
import org.junit.Test;

public class Issue235 extends AbstractResolutionTest{
    @Test
    public void issue235() throws ParseException {
        CompilationUnit cu = parseSample("Issue235");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "Foo");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        ExpressionStmt stmt;
        ObjectCreationExpr expression;
        MethodDeclaration m;

        m = Navigator.demandMethod(cls, "correct1");
        stmt = (ExpressionStmt) m.getBody().get().getStatements().get(0);
        expression = (ObjectCreationExpr) stmt.getExpression();
        Assert.assertNotNull(javaParserFacade.convertToUsage(expression.getType()));

        m = Navigator.demandMethod(cls, "correct2");
        stmt = (ExpressionStmt) m.getBody().get().getStatements().get(0);
        expression = (ObjectCreationExpr) stmt.getExpression();
        Assert.assertNotNull(javaParserFacade.convertToUsage(expression.getType()));

        m = Navigator.demandMethod(cls, "failing");
        stmt = (ExpressionStmt) m.getBody().get().getStatements().get(0);
        expression = (ObjectCreationExpr) stmt.getExpression();
        Assert.assertNotNull(javaParserFacade.convertToUsage(expression.getType()));
    }
}
