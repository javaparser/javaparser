package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.SwitchStmt;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import org.junit.Test;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class EnumResolutionTest extends AbstractResolutionTest {

    @Test
    public void switchOnEnum() throws ParseException {
        CompilationUnit cu = parseSample("SwitchOnEnum");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SwitchOnEnum");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        SwitchStmt switchStmt = Navigator.findSwitch(method);
        Expression expression = switchStmt.getEntries().get(0).getLabel();

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(new JreTypeSolver()).solve(expression);
        assertTrue(ref.isSolved());
        assertEquals("SwitchOnEnum.MyEnum", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void enumAndStaticInitializer() throws ParseException {
        CompilationUnit cu = parseSample("EnumAndStaticInitializer");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        MethodCallExpr call = Navigator.findMethodCall(clazz, "put");

        Type ref = JavaParserFacade.get(new JreTypeSolver()).getType(call);
        assertEquals("MyClass.Primitive", ref.describe());
    }

}
