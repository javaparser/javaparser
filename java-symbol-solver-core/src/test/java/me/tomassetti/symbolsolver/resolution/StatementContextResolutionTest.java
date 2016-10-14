package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

public class StatementContextResolutionTest extends AbstractResolutionTest {

    @Test
    public void resolveLocalVariableInParentOfParent() throws ParseException {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo1");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s");

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(new JreTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void resolveLocalVariableInParent() throws ParseException {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo3");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s");

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(new JreTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void resolveLocalVariableInSameParent() throws ParseException {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo2");
        NameExpr nameExpr = Navigator.findNameExpression(method, "s");

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(new JreTypeSolver()).solve(nameExpr);
        assertTrue(ref.isSolved());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void resolveLocalAndSeveralAnnidatedLevels() throws ParseException {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo4");
        MethodCallExpr call = Navigator.findMethodCall(method, "add");

        TypeSolver typeSolver = new JreTypeSolver();

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(typeSolver).solve(call.getScope());
        assertTrue(ref.isSolved());
        assertEquals("java.util.List<Comment>", ref.getCorrespondingDeclaration().getType().describe());

        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);
        assertEquals("add", methodUsage.getName());
    }

    @Test
    public void resolveMethodOnGenericClass() throws ParseException {
        CompilationUnit cu = parseSample("LocalVariableInParent");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "LocalVariableInParent");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "foo5");
        MethodCallExpr call = Navigator.findMethodCall(method, "add");

        TypeSolver typeSolver = new JreTypeSolver();

        SymbolReference<? extends ValueDeclaration> ref = JavaParserFacade.get(typeSolver).solve(call.getScope());
        assertTrue(ref.isSolved());
        assertEquals("java.util.List<Comment>", ref.getCorrespondingDeclaration().getType().describe());

        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);
        assertEquals("add", methodUsage.getName());
    }

}
