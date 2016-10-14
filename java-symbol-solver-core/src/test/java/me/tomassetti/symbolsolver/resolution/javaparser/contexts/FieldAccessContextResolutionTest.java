package me.tomassetti.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;

import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * @author Malte Langkabel
 */
public class FieldAccessContextResolutionTest extends AbstractResolutionTest {

    @Test
    public void solveMethodCallInFieldAccessContext() throws ParseException {
        CompilationUnit cu = parseSample("MethodCalls");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar2");
        MethodCallExpr methodCallExpr = Navigator.findMethodCall(method, "getSelf");
        
        TypeSolver typeSolver = new JreTypeSolver();
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
        
        assertEquals(methodUsage.getName(), "getSelf");
    }
}
