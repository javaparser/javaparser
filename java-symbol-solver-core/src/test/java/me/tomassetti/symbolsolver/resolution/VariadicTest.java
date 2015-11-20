package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.*;

public class VariadicTest extends AbstractTest{

    @Test
    public void issue7() throws ParseException {
        CompilationUnit cu = parseSample("Generics_issue7");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo3");

        ReturnStmt stmt = (ReturnStmt)method.getBody().getStmts().get(0);
        Expression expression = stmt.getExpr();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new JreTypeSolver());
        TypeUsage typeUsage = javaParserFacade.getType(expression);
        assertEquals(true, typeUsage.isReferenceType());
        assertEquals(List.class.getCanonicalName(), typeUsage.asReferenceTypeUsage().getQualifiedName());
        assertEquals("java.util.List<java.lang.Long>", typeUsage.describe());
    }

}
