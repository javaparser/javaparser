package com.github.javaparser.symbolsolver;

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
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.Arrays;
import java.util.Collection;

class Issue235Test extends AbstractResolutionTest{

    static Collection<String> data() {
        return Arrays.asList(
                "new_Bar_Baz_direct",
                "new_Bar_Baz",
                "new_Bar",
                "new_Foo_Bar"
        );
    }

    @ParameterizedTest
    @MethodSource("data")
    void issue235(String method) {
        CompilationUnit cu = parseSample("Issue235");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "Foo");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodDeclaration m = Navigator.demandMethod(cls, method);
        ExpressionStmt stmt = (ExpressionStmt) m.getBody().get().getStatements().get(0);
        ObjectCreationExpr expression = (ObjectCreationExpr) stmt.getExpression();
        Assertions.assertNotNull(javaParserFacade.convertToUsage(expression.getType()));
    }
}
