package me.tomassetti.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;

import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.javaparsermodel.contexts.MethodCallExprContext;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.io.File;
import java.util.Collections;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Malte Langkabel
 */
public class MethodCallExprContextResolutionTest extends AbstractResolutionTest {

    @Test
    public void solveNestedMethodCallExprContextWithoutScope() throws ParseException {
        CompilationUnit cu = parseSample("MethodCalls");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar1");
        MethodCallExpr methodCallExpr = Navigator.findMethodCall(method, "foo");
        
        File src = adaptPath(new File("src/test/resources"));
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        
        Context context = new MethodCallExprContext(methodCallExpr, combinedTypeSolver);
        
        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo", Collections.emptyList(), combinedTypeSolver);
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
    }
}
