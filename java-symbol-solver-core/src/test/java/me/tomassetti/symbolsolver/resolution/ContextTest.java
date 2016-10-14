package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import me.tomassetti.symbolsolver.AbstractTest;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.typesolvers.*;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;

import static org.easymock.EasyMock.*;
import static org.junit.Assert.assertEquals;

public class ContextTest extends AbstractTest {

    private CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = ContextTest.class.getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        return JavaParser.parse(is);
    }

    @Test
    public void resolveDeclaredFieldReference() throws ParseException {
        CompilationUnit cu = parseSample("ReferencesToField");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToField");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferencesToFieldExtendingClass");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "ReferenceToParameter");
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
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ClassDeclaration compilationUnitDecl = createMock(ClassDeclaration.class);
        expect(compilationUnitDecl.getName()).andReturn("CompilationUnit");
        expect(compilationUnitDecl.getQualifiedName()).andReturn("com.github.javaparser.ast.CompilationUnit");
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("com.github.javaparser.ast.CompilationUnit")).andReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, compilationUnitDecl);
        SymbolReference<? extends TypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertEquals(true, ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, compilationUnitDecl);
    }

    @Test
    public void resolveReferenceUsingQualifiedName() throws ParseException {
        CompilationUnit cu = parseSample("Navigator2");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
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
        SymbolReference<? extends TypeDeclaration> ref = symbolSolver.solveType("com.github.javaparser.ast.CompilationUnit", param);

        assertEquals(true, ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, compilationUnitDecl);
    }

    @Test
    public void resolveReferenceToClassesInTheSamePackage() throws ParseException {
        CompilationUnit cu = parseSample("Navigator3");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        Parameter param = method.getParameters().get(0);

        ClassDeclaration compilationUnitDecl = createMock(ClassDeclaration.class);
        expect(compilationUnitDecl.getName()).andReturn("CompilationUnit");
        expect(compilationUnitDecl.getQualifiedName()).andReturn("my.packagez.CompilationUnit");
        TypeSolver typeSolver = createMock(TypeSolver.class);
        expect(typeSolver.tryToSolveType("my.packagez.CompilationUnit")).andReturn(SymbolReference.solved(compilationUnitDecl));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        replay(typeSolver, compilationUnitDecl);
        SymbolReference<? extends TypeDeclaration> ref = symbolSolver.solveType("CompilationUnit", param);

        assertEquals(true, ref.isSolved());
        assertEquals("CompilationUnit", ref.getCorrespondingDeclaration().getName());
        assertEquals("my.packagez.CompilationUnit", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, compilationUnitDecl);
    }

    @Test
    public void resolveReferenceToClassInJavaLang() throws ParseException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
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
        SymbolReference<? extends TypeDeclaration> ref = symbolSolver.solveType("String", param);

        assertEquals(true, ref.isSolved());
        assertEquals("String", ref.getCorrespondingDeclaration().getName());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getQualifiedName());

        verify(typeSolver, stringDecl);
    }

    @Test
    public void resolveReferenceToMethod() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToGetTypes = Navigator.findMethodCall(method, "getTypes");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);

        MethodUsage ref = symbolSolver.solveMethod("getTypes", Collections.emptyList(), callToGetTypes);

        assertEquals("getTypes", ref.getName());
        assertEquals("com.github.javaparser.ast.CompilationUnit", ref.declaringType().getQualifiedName());

        //verify(typeSolver);
    }

    @Test
    public void resolveCascadeOfReferencesToMethod() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration referencesToField = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(referencesToField, "findType");
        MethodCallExpr callToStream = Navigator.findMethodCall(method, "stream");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("stream", Collections.emptyList(), callToStream);

        assertEquals("stream", ref.getName());
        assertEquals("java.util.Collection", ref.declaringType().getQualifiedName());
    }
    
    @Test
    public void resolveReferenceToMethodCalledOnArrayAccess() throws ParseException, IOException {
        CompilationUnit cu = parseSample("ArrayAccess");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "access");
        MethodCallExpr callToTrim = Navigator.findMethodCall(method, "trim");
        
        File src = new File("src/test/resources");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JavaParserTypeSolver(src));
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("trim", Collections.emptyList(), callToTrim);

        assertEquals("trim", ref.getName());
        assertEquals("java.lang.String", ref.declaringType().getQualifiedName());
    }

    @Test
    public void resolveReferenceToJreType() throws ParseException, IOException {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        com.github.javaparser.ast.type.Type streamJavaParserType = method.getParameters().get(0).getType();

        TypeSolver typeSolver = new JreTypeSolver();
        Type streamType = JavaParserFacade.get(typeSolver).convert(streamJavaParserType, method);

        assertEquals("java.util.stream.Stream<java.lang.String>",streamType.describe());
    }

    @Test
    public void resolveReferenceToMethodWithLambda() throws ParseException, IOException {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr methodCallExpr = Navigator.findMethodCall(method, "filter");

        TypeSolver typeSolver = new JreTypeSolver();
        Type ref = JavaParserFacade.get(typeSolver).getType(methodCallExpr);

        assertEquals("java.util.stream.Stream<java.lang.String>", ref.describe());
        assertEquals(1, ref.asReferenceType().typeParametersValues().size());
        assertEquals("java.lang.String", ref.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveReferenceToLambdaParamBase() throws ParseException, IOException {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        NameExpr refToT = Navigator.findNameExpression(method, "t");

        TypeSolver typeSolver = new JreTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        Type ref = javaParserFacade.getType(refToT);

        assertEquals("? super java.lang.String", ref.describe());
    }

    @Test
    public void resolveReferenceToLambdaParamSimplified() throws ParseException, IOException {
        CompilationUnit cu = parseSample("NavigatorSimplified");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr call = Navigator.findMethodCall(method, "isEmpty");

        TypeSolver typeSolver = new JreTypeSolver();
        SymbolSolver symbolSolver = new SymbolSolver(typeSolver);
        MethodUsage ref = symbolSolver.solveMethod("isEmpty", Collections.emptyList(), call);

        assertEquals("isEmpty", ref.getName());
        assertEquals("java.lang.String", ref.declaringType().getQualifiedName());
    }

    @Test
    public void resolveGenericReturnTypeOfMethodInJar() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr call = Navigator.findMethodCall(method, "getTypes");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("getTypes", methodUsage.getName());
        assertEquals("java.util.List<com.github.javaparser.ast.body.TypeDeclaration>", methodUsage.returnType().describe());
        assertEquals(1, methodUsage.returnType().asReferenceType().typeParametersValues().size());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", methodUsage.returnType().asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveTypeUsageOfFirstMethodInGenericClass() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetTypes = Navigator.findMethodCall(method, "getTypes");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage filterUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToGetTypes);

        assertEquals("java.util.List<com.github.javaparser.ast.body.TypeDeclaration>", filterUsage.returnType().describe());
        assertEquals(1, filterUsage.returnType().asReferenceType().typeParametersValues().size());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", filterUsage.returnType().asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveTypeUsageOfMethodInGenericClass() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToStream = Navigator.findMethodCall(method, "stream");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage filterUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToStream);

        assertEquals("java.util.stream.Stream<com.github.javaparser.ast.body.TypeDeclaration>", filterUsage.returnType().describe());
    }

    @Test
    public void resolveTypeUsageOfCascadeMethodInGenericClass() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToFilter = Navigator.findMethodCall(method, "filter");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage filterUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToFilter);

        assertEquals("java.util.stream.Stream<com.github.javaparser.ast.body.TypeDeclaration>", filterUsage.returnType().describe());
    }

    @Test
    public void resolveLambdaType() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToFilter = Navigator.findMethodCall(method, "filter");
        Expression lambdaExpr = callToFilter.getArgs().get(0);

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        Type typeOfLambdaExpr = JavaParserFacade.get(typeSolver).getType(lambdaExpr);

        assertEquals("java.util.function.Predicate<com.github.javaparser.ast.body.TypeDeclaration>", typeOfLambdaExpr.describe());
    }

    @Test
    public void resolveReferenceToLambdaParam() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetName = Navigator.findMethodCall(method, "getName");
        Expression referenceToT = callToGetName.getScope();

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        Type typeOfT = JavaParserFacade.get(typeSolver).getType(referenceToT);

        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", typeOfT.describe());
    }

    @Test
    public void resolveReferenceToCallOnLambdaParam() throws ParseException, IOException {
        CompilationUnit cu = parseSample("Navigator");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Navigator");
        MethodDeclaration method = Navigator.demandMethod(clazz, "findType");
        MethodCallExpr callToGetName = Navigator.findMethodCall(method, "getName");

        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JarTypeSolver(pathToJar));
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(callToGetName);

        assertEquals("getName", methodUsage.getName());
        assertEquals("com.github.javaparser.ast.body.TypeDeclaration", methodUsage.declaringType().getQualifiedName());
    }

    @Test
    public void resolveReferenceToOverloadMethodWithNullParam() throws ParseException, IOException {
        CompilationUnit cu = parseSample("OverloadedMethods");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m1");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded");

        JreTypeSolver typeSolver = new JreTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.String", ref.getParamTypes().get(0).describe());
    }

    @Test
    public void resolveReferenceToOverloadMethodFindStricter() throws ParseException, IOException {
        CompilationUnit cu = parseSample("OverloadedMethods");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m2");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded");

        JreTypeSolver typeSolver = new JreTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.String", ref.getParamTypes().get(0).describe());
    }

    @Test
    public void resolveReferenceToOverloadMethodFindOnlyCompatible() throws ParseException, IOException {
        CompilationUnit cu = parseSample("OverloadedMethods");
        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "OverloadedMethods");
        MethodDeclaration method = Navigator.demandMethod(clazz, "m3");
        MethodCallExpr call = Navigator.findMethodCall(method, "overloaded");

        JreTypeSolver typeSolver = new JreTypeSolver();
        MethodUsage ref = JavaParserFacade.get(typeSolver).solveMethodAsUsage(call);

        assertEquals("overloaded", ref.getName());
        assertEquals(1, ref.getNoParams());
        assertEquals("java.lang.Object", ref.getParamTypes().get(0).describe());
    }

}
