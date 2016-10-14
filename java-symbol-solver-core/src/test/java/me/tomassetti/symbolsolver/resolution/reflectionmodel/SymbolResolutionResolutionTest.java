package me.tomassetti.symbolsolver.resolution.reflectionmodel;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.resolution.AbstractResolutionTest;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class SymbolResolutionResolutionTest extends AbstractResolutionTest {

    @Test
    public void getTypeOfField() throws ParseException {
        CompilationUnit cu = parseSample("ReflectionFieldOfItself");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        VariableDeclarator field = Navigator.demandField(clazz, "PUBLIC");

        TypeSolver typeSolver = new JreTypeSolver();
        Type ref = JavaParserFacade.get(typeSolver).getType(field);
        assertEquals("int", ref.describe());
    }

    @Test
    public void getTypeOfFieldAccess() throws ParseException {
        CompilationUnit cu = parseSample("ReflectionFieldOfItself");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        VariableDeclarator field = Navigator.demandField(clazz, "PUBLIC");

        TypeSolver typeSolver = new JreTypeSolver();
        Type ref = JavaParserFacade.get(typeSolver).getType(field.getInit());
        assertEquals("int", ref.describe());
    }

    @Test
    public void conditionalExpressionExample() throws ParseException {
        CompilationUnit cu = parseSample("JreConditionalExpression");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);
        Expression expression = returnStmt.getExpr();

        TypeSolver typeSolver = new JreTypeSolver();
        Type ref = JavaParserFacade.get(typeSolver).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }

    @Test
    public void conditionalExpressionExampleFollowUp1() throws ParseException {
        CompilationUnit cu = parseSample("JreConditionalExpression");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");
        MethodCallExpr expression = Navigator.findMethodCall(method, "next");

        TypeSolver typeSolver = new JreTypeSolver();
        Type ref = JavaParserFacade.get(typeSolver).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }

}
