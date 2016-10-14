package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.NameExpr;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class QualifiedNameResolutionTest extends AbstractResolutionTest {

    @Test
    public void resolveLocalVariableInParentOfParent() throws ParseException {
        CompilationUnit cu = parseSample("QualifiedNameTest");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "QualifiedNameTest");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo1");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s");

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(new JreTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.util.Scanner", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

}
