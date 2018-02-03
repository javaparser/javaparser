package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class Issue128 extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() throws IOException {
        File srcDir = adaptPath(new File("src/test/resources/issue128"));
        typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(srcDir));
    }

    @Test
    public void verifyJavaTestClassIsSolved() {
        typeSolver.solveType("foo.JavaTest");
    }

    @Test
    public void loopOnStaticallyImportedType() {
        CompilationUnit cu = parseSampleWithStandardExtension("issue128/foo/Issue128");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "JavaTest");
        ExpressionStmt expressionStmt = (ExpressionStmt)clazz.getMethodsByName("test").get(0).getBody().get().getStatement(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) expressionStmt.getExpression();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        assertEquals(false, javaParserFacade.solve(methodCallExpr).isSolved());
    }
}
