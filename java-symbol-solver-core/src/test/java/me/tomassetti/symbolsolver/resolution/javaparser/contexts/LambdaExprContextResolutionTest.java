package me.tomassetti.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;

import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.javaparsermodel.contexts.LambdaExprContext;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Malte Langkabel
 */
public class LambdaExprContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
    }

    @Test
    public void solveParameterOfLambdaInMethodCallExpr() throws ParseException {
        CompilationUnit cu = parseSample("Lambda");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "lambdaMap");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);
        MethodCallExpr methodCallExpr = (MethodCallExpr)returnStmt.getExpr();
        LambdaExpr lambdaExpr = (LambdaExpr)methodCallExpr.getArgs().get(0);
        
        Context context = new LambdaExprContext(lambdaExpr, typeSolver);
        
        Optional<Value> ref = context.solveSymbolAsValue("p", typeSolver);
        assertTrue(ref.isPresent());
        assertEquals("? super java.lang.String", ref.get().getUsage().describe());
    }

    @Test
    public void solveParameterOfLambdaInFieldDecl() throws ParseException {
        CompilationUnit cu = parseSample("Lambda");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        VariableDeclarator field = Navigator.demandField(clazz, "functional");
        LambdaExpr lambdaExpr = (LambdaExpr)field.getInit();
        
        File src = new File("src/test/resources");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        
        Context context = new LambdaExprContext(lambdaExpr, combinedTypeSolver);
        
        Optional<Value> ref = context.solveSymbolAsValue("p", typeSolver);
        assertTrue(ref.isPresent());
        assertEquals("java.lang.String", ref.get().getUsage().describe());
    }
    
    @Test
    public void solveParameterOfLambdaInVarDecl() throws ParseException {
        CompilationUnit cu = parseSample("Lambda");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testFunctionalVar");
        VariableDeclarator varDecl = Navigator.demandVariableDeclaration(method, "a");
        LambdaExpr lambdaExpr = (LambdaExpr)varDecl.getInit();
                
        File src = new File("src/test/resources");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        
        Context context = new LambdaExprContext(lambdaExpr, combinedTypeSolver);
        
        Optional<Value> ref = context.solveSymbolAsValue("p", typeSolver);
        assertTrue(ref.isPresent());
        assertEquals("java.lang.String", ref.get().getUsage().describe());
    }
}
