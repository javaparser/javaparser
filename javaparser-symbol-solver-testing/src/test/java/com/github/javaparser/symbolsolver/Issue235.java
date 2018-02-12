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
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public class Issue235 extends AbstractResolutionTest{
    private final String method;

    public Issue235(String method) {
        this.method = method;
    }

    @Parameterized.Parameters(name = "{0}")
    public static Collection<String> data() throws Exception {
        return Arrays.asList(
                "new_Bar_Baz_direct",
                "new_Bar_Baz",
                "new_Bar",
                "new_Foo_Bar"
        );
    }

    @Test
    public void issue235() {
        CompilationUnit cu = parseSample("Issue235");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "Foo");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodDeclaration m = Navigator.demandMethod(cls, this.method);
        ExpressionStmt stmt = (ExpressionStmt) m.getBody().get().getStatements().get(0);
        ObjectCreationExpr expression = (ObjectCreationExpr) stmt.getExpression();
        Assert.assertNotNull(javaParserFacade.convertToUsage(expression.getType()));
    }
}
