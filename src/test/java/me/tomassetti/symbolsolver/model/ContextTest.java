package me.tomassetti.symbolsolver.model;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.typesolvers.JarTypeSolver;
import org.junit.Test;
import static org.easymock.EasyMock.*;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.Collections;

import static org.junit.Assert.*;

public class ContextTest {

    private CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = ContextTest.class.getClassLoader().getResourceAsStream(sampleName + ".java.txt");
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

    @Test
    public void resolveReferenceUsingQualifiedName() throws ParseException {
        CompilationUnit cu = parseSample("Navigator2");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ClassDeclaration compilationUnitDecl = createMock(ClassDeclaration.class);
        expect(compilationUnitDecl.getName()).andReturn("CompilationUnit");
        expect(compilationUnitDecl.getQualifiedName()).andReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("java.lang.com.github.javaparser.ast.CompilationUnit")).andReturn(SymbolReference.unsolved(ClassDeclaration.class));
        expect(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).andReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, compilationUnitDecl);
        SymbolReference<TypeDeclaration> ref = symbolSolver.solveType("com.github.javaparser.ast.CompilationUnit", param);

        assertEquals(true, ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, compilationUnitDecl);
    }

    @Test
    public void resolveReferenceToClassesInTheSamePackage() throws ParseException {
        CompilationUnit cu = parseSample("Navigator3");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ClassDeclaration compilationUnitDecl = createMock(ClassDeclaration.class);
        expect(compilationUnitDecl.getName()).andReturn("CompilationUnit");
        expect(compilationUnitDecl.getQualifiedName()).andReturn("my.packagez.CompilationUnit");
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("my.packagez.CompilationUnit")).andReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, compilationUnitDecl);
        SymbolReference<TypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertEquals(true, ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("my.packagez.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, compilationUnitDecl);
    }

    @Test
    public void resolveReferenceToClassInJavaLang() throws ParseException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(1);

        ClassDeclaration stringDecl = createMock(ClassDeclaration.class);
        expect(stringDecl.getName()).andReturn("String");
        expect(stringDecl.getQualifiedName()).andReturn("java.lang.String");
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("me.tomassetti.symbolsolver.javaparser.String")).andReturn(SymbolReference.unsolved(TypeDeclaration.class));
        expect(typeSolver.tryToSolveType("java.lang.String")).andReturn(SymbolReference.solved(stringDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, stringDecl);
        SymbolReference<TypeDeclaration> ref = symbolSolver.solveType("String", param);

        assertEquals(true, ref.isSolved());
        assertEquals("String", ref.getCorrespondingDeclaration().getName());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, stringDecl);
    }

    @Test
    public void resolveReferenceToMethod() throws ParseException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToGetTypes = Navigator.findMethodCall(method, "getTypes");

        Context compilationUnitCtx = createMock(Context.class);
        me.tomassetti.symbolsolver.model.MethodDeclaration getTypes = createMock(me.tomassetti.symbolsolver.model.MethodDeclaration.class);
        expect(getTypes.getName()).andReturn("getTypes");

        ClassDeclaration compilationUnit = createMock(ClassDeclaration.class);
        expect(compilationUnit.getName()).andReturn("CompilationUnit");
        expect(compilationUnit.getQualifiedName()).andReturn("com.github.javaparser.ast.CompilationUnit");
        expect(compilationUnit.isType()).andReturn(true);
        expect(compilationUnit.asTypeDeclaration()).andReturn(compilationUnit);
        expect(compilationUnit.getContext()).andReturn(compilationUnitCtx);
        expect(compilationUnit.solveMethod("getTypes", Collections.emptyList())).andReturn(SymbolReference.solved(getTypes));
        expect(getTypes.getType()).andReturn(compilationUnit);
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).andReturn(SymbolReference.solved(compilationUnit));
        //expect(compilationUnitCtx.solveMethod("getTypes", Collections.emptyList(), typeSolver)).andReturn(SymbolReference.solved(getTypes));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, compilationUnit, compilationUnitCtx, getTypes);
        SymbolReference<me.tomassetti.symbolsolver.model.MethodDeclaration> ref = symbolSolver.solveMethod("getTypes", Collections.emptyList(), callToGetTypes);

        assertEquals(true, ref.isSolved());
        assertEquals("getTypes", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getType().getQualifiedName());

        verify(typeSolver);
    }

    @Test
    public void resolveCascadeOfReferencesToMethod() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToStream = Navigator.findMethodCall(method, "stream");

        String pathToJar = "src/test/resources/javaparser-core-2.1.0.jar";
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference<me.tomassetti.symbolsolver.model.MethodDeclaration> ref = symbolSolver.solveMethod("stream", Collections.emptyList(), callToStream);

        assertEquals(true, ref.isSolved());
        assertEquals("stream", ref.getCorrespondingDeclaration().getName());
        assertEquals("java.util.Collection", ref.getCorrespondingDeclaration().getType().getQualifiedName());
    }

    @Test
    public void resolveReferenceToLambdaParam() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetName = Navigator.findMethodCall(method, "getName");

        String pathToJar = "src/test/resources/javaparser-core-2.1.0.jar";
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        SymbolReference<me.tomassetti.symbolsolver.model.MethodDeclaration> ref = symbolSolver.solveMethod("stream", Collections.emptyList(), callToGetName);

        assertEquals(true, ref.isSolved());
        assertEquals("getName", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", ref.getCorrespondingDeclaration().getType().getQualifiedName());
    }

}
