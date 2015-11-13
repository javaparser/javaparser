package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class LambdaTest extends AbstractTest {

    @Test
    public void lambdaMapParameter() throws ParseException {
        CompilationUnit cu = parseSample("Lambda");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "lambdaMap");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);
        MethodCallExpr methodCallExpr = (MethodCallExpr)returnStmt.getExpr();
        Expression expression = methodCallExpr.getArgs().get(0);

        JavaParserFacade javaParserFacade = JavaParserFacade.get(new JreTypeSolver());
        TypeUsage type = javaParserFacade.getType(expression);
        assertEquals("java.util.function.Function<? super java.lang.String, ? extends java.lang.String>", type.describe());
    }

    @Test
    public void lambdaMap() throws ParseException {
        CompilationUnit cu = parseSample("Lambda");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Agenda");
        MethodDeclaration method = Navigator.demandMethod(clazz, "lambdaMap");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);
        Expression expression = returnStmt.getExpr();

        JavaParserFacade javaParserFacade = JavaParserFacade.get(new JreTypeSolver());
        TypeUsage type = javaParserFacade.getType(expression);
        assertEquals("java.util.stream.Stream<java.lang.String>", type.describe());
    }


}
