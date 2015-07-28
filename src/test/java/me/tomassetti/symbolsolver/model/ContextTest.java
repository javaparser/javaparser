package me.tomassetti.symbolsolver.model;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import org.junit.Test;

import java.io.InputStream;

import static org.junit.Assert.*;

/**
 * Created by federico on 28/07/15.
 */
public class ContextTest {

    private CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = ContextTest.class.getClassLoader().getResourceAsStream(sampleName + ".java");
        return JavaParser.parse(is);
    }

    @Test
    public void firstTest() throws ParseException {
        CompilationUnit cu = parseSample("ReferencesToField");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToField");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method1");
        ExpressionStmt stmt = (ExpressionStmt)method1.getBody().getStmts().get(0);
        AssignExpr assignExpr = (AssignExpr)stmt.getExpression();

        SymbolSolver symbolSolver = new SymbolSolver();
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertEquals(true, symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertEquals(true, symbolReference.getCorrespondingDeclaration().isField());
    }

}
