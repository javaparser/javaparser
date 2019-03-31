package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue156Test extends AbstractResolutionTest {

    @Test
    void testFieldAccessThroughClassAndThis() {

        CompilationUnit cu = parseSample("Issue156");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Issue156");
          List<MethodCallExpr> methods = clazz.getChildNodes().get(3).getChildNodes().get(1).findAll(MethodCallExpr.class);
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        assertEquals("char", javaParserFacade.getType(methods.get(0)).describe());
    }
}
