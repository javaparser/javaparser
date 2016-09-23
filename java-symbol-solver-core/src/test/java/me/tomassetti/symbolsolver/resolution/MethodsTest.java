package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class MethodsTest extends AbstractTest{

    @Test
    public void accessMethodThroughSuper() throws ParseException {
        CompilationUnit cu = parseSample("AccessThroughSuper");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AccessThroughSuper.SubClass");
        MethodDeclaration method = Navigator.demandMethod(clazz, "methodTest");
        ReturnStmt returnStmt = (ReturnStmt)method.getBody().getStmts().get(0);
        Expression expression = returnStmt.getExpr();

        TypeUsage ref = JavaParserFacade.get(new JreTypeSolver()).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }
}
