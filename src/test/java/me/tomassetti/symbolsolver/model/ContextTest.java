package me.tomassetti.symbolsolver.model;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import org.junit.Test;
import static org.easymock.EasyMock.*;

import java.io.InputStream;

import static org.junit.Assert.*;

/**
 * Created by federico on 28/07/15.
 */
public class ContextTest {

    private CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = ContextTest.class.getClassLoader().getResourceAsStream(sampleName + ".java");
        return JavaParser.parse(is);
    }

    @Test
    public void resolveDeclaredFieldReference() throws ParseException {
        CompilationUnit cu = parseSample("ReferencesToField");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToField");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method1");
        ExpressionStmt stmt = (ExpressionStmt)method1.getBody().getStmts().get(0);
        AssignExpr assignExpr = (AssignExpr)stmt.getExpression();

        SymbolSolver symbolSolver = new SymbolSolver(new DummyTypeSolver());
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertEquals(true, symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertEquals(true, symbolReference.getCorrespondingDeclaration().isField());
    }

    @Test
    public void resolveInheritedFieldReference() throws ParseException {
        CompilationUnit cu = parseSample("ReferencesToField");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToFieldExtendingClass");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "method2");
        ExpressionStmt stmt = (ExpressionStmt)method1.getBody().getStmts().get(0);
        AssignExpr assignExpr = (AssignExpr)stmt.getExpression();

        SymbolSolver symbolSolver = new SymbolSolver(new DummyTypeSolver());
        SymbolReference symbolReference = symbolSolver.solveSymbol("i", assignExpr.getTarget());

        assertEquals(true, symbolReference.isSolved());
        assertEquals("i", symbolReference.getCorrespondingDeclaration().getName());
        assertEquals(true, symbolReference.getCorrespondingDeclaration().isField());
    }

    @Test
    public void resolveParameterReference() throws ParseException {
        CompilationUnit cu = parseSample("ReferencesToParameter");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferenceToParameter");
        MethodDeclaration method1 = Navigator.demandMethod(referencesToField, "aMethod");
        NameExpr foo = Navigator.findNameExpression(method1, "foo");

        SymbolSolver symbolSolver = new SymbolSolver(new DummyTypeSolver());
        SymbolReference symbolReference = symbolSolver.solveSymbol("foo", foo);

        assertEquals(true, symbolReference.isSolved());
        assertEquals("foo", symbolReference.getCorrespondingDeclaration().getName());
        assertEquals(true, symbolReference.getCorrespondingDeclaration().isParameter());
    }

    @Test
    public void resolveReferenceToImportedType() throws ParseException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ClassDeclaration compilationUnitDecl = createMock(ClassDeclaration.class);
        expect(compilationUnitDecl.getName()).andReturn("CompilationUnit");
        expect(compilationUnitDecl.getQualifiedName()).andReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).andReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, compilationUnitDecl);
        SymbolReference<TypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertEquals(true, ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, compilationUnitDecl);
    }


}
