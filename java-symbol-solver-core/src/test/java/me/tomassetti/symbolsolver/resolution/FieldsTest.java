package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;

public class FieldsTest extends AbstractTest{

    @Test
    public void accessFieldThroughThis() throws ParseException {
        CompilationUnit cu = parseSample("AccessFieldThroughThis");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AccessFieldThroughThis");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getLabel2");
        ReturnStmt returnStmt = (ReturnStmt)method.getBody().getStmts().get(0);
        Expression expression = returnStmt.getExpr();

        TypeUsage ref = JavaParserFacade.get(new JreTypeSolver()).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }
    
    @Test
    public void accessFieldThroughThisWithCompetingSymbolInParentContext() throws ParseException {
        CompilationUnit cu = parseSample("AccessFieldThroughThis");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AccessFieldThroughThis");
        MethodDeclaration method = Navigator.demandMethod(clazz, "setLabel");
        ExpressionStmt expressionStmt = (ExpressionStmt)method.getBody().getStmts().get(0);
        AssignExpr assignExpr = (AssignExpr)expressionStmt.getExpression();
        FieldAccessExpr fieldAccessExpr = (FieldAccessExpr)assignExpr.getTarget();
        
        File src = new File("src/test/resources");
        JavaParserTypeSolver typeSolver = new JavaParserTypeSolver(src);
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference<? extends ValueDeclaration> ref = symbolSolver.solveSymbol(fieldAccessExpr.getField(), fieldAccessExpr);

        assertTrue(ref.isSolved());
        assertTrue(ref.getCorrespondingDeclaration().isField());
    }
    
    @Test
    public void accessFieldThroughSuper() throws ParseException {
        CompilationUnit cu = parseSample("AccessThroughSuper");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AccessThroughSuper.SubClass");
        MethodDeclaration method = Navigator.demandMethod(clazz, "fieldTest");
        ReturnStmt returnStmt = (ReturnStmt)method.getBody().getStmts().get(0);
        Expression expression = returnStmt.getExpr();

        TypeUsage ref = JavaParserFacade.get(new JreTypeSolver()).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }
}
