package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class FieldsTest extends AbstractTest{

    @Test
    public void accessFieldThroughThis() throws ParseException {
        CompilationUnit cu = parseSample("AccessFieldThroughThis");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AccessFieldThroughThis");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getLabel2");
        ReturnStmt returnStmt = (ReturnStmt)method.getBody().getStmts().get(0);
        Expression expression = returnStmt.getExpr();

        TypeUsage ref = JavaParserFacade.get(new JreTypeSolver()).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }


}
