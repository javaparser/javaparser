package me.tomassetti.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.javaparsermodel.contexts.CompilationUnitContext;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.usages.typesystem.NullType;
import me.tomassetti.symbolsolver.model.usages.typesystem.PrimitiveType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.AbstractResolutionTest;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.DummyTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JarTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.easymock.EasyMock;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Federico Tomassetti
 */
public class CompilationUnitContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
    }

    @Test
    public void getParent() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        Context context = new CompilationUnitContext(cu, typeSolver);

        assertTrue(null == context.getParent());
    }

    @Test
    public void solveExistingGenericType() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        Context context = new CompilationUnitContext(cu, typeSolver);

        Optional<Type> a = context.solveGenericType("A", new DummyTypeSolver());
        Optional<Type> b = context.solveGenericType("B", new DummyTypeSolver());
        Optional<Type> c = context.solveGenericType("C", new DummyTypeSolver());

        assertEquals(false, a.isPresent());
        assertEquals(false, b.isPresent());
        assertEquals(false, c.isPresent());
    }

    @Test
    public void solveUnexistingGenericType() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        Context context = new CompilationUnitContext(cu, typeSolver);

        Optional<Type> d = context.solveGenericType("D", new DummyTypeSolver());

        assertEquals(false, d.isPresent());
    }

    @Test
    public void solveSymbolReferringToStaticallyImportedValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JreTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("out", typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("java.io.PrintStream", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void solveSymbolReferringToStaticallyImportedUsingAsteriskValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JreTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("err", typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("java.io.PrintStream", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void solveSymbolReferringToStaticField() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("java.lang.System.out", new JreTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("java.io.PrintStream", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void solveSymbolAsValueReferringToStaticallyImportedValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JreTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        Optional<Value> ref = context.solveSymbolAsValue("out", typeSolver);
        assertEquals(true, ref.isPresent());
        assertEquals("java.io.PrintStream", ref.get().getUsage().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToStaticallyImportedUsingAsteriskValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JreTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        Optional<Value> ref = context.solveSymbolAsValue("err", typeSolver);
        assertEquals(true, ref.isPresent());
        assertEquals("java.io.PrintStream", ref.get().getUsage().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToStaticField() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("java.lang.System.out", new JreTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("java.io.PrintStream", ref.get().getUsage().describe());
    }

    @Test
    public void solveTypeInSamePackage() throws ParseException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        TypeDeclaration otherClass = EasyMock.createMock(TypeDeclaration.class);
        EasyMock.expect(otherClass.getQualifiedName()).andReturn("com.foo.OtherClassInSamePackage");
        DummyTypeSolver dummyTypeSolver = new DummyTypeSolver();
        dummyTypeSolver.addDeclaration("com.foo.OtherClassInSamePackage", otherClass);
        EasyMock.replay(otherClass);

        SymbolReference<TypeDeclaration> ref = context.solveType("OtherClassInSamePackage", dummyTypeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("com.foo.OtherClassInSamePackage", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    public void solveTypeImported() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        SymbolReference<TypeDeclaration> ref = context.solveType("Assert", new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        assertEquals(true, ref.isSolved());
        assertEquals("org.junit.Assert", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    public void solveTypeNotImported() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        SymbolReference<TypeDeclaration> ref = context.solveType("org.junit.Assume", new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        assertEquals(true, ref.isSolved());
        assertEquals("org.junit.Assume", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    public void solveMethodStaticallyImportedWithAsterisk() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        typeSolver.add(new JreTypeSolver());

        SymbolReference<MethodDeclaration> ref = context.solveMethod("assertFalse", ImmutableList.of(PrimitiveType.BOOLEAN), typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("assertFalse", ref.getCorrespondingDeclaration().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNoParams());
        assertEquals("boolean", ref.getCorrespondingDeclaration().getParam(0).getType().describe());
        assertEquals(true, ref.getCorrespondingDeclaration().getParam(0).getType().isPrimitive());
    }

    @Test
    public void solveMethodStaticallyImportedWithoutAsterisk() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        typeSolver.add(new JreTypeSolver());

        SymbolReference<MethodDeclaration> ref = context.solveMethod("assertEquals", ImmutableList.of(NullType.INSTANCE, NullType.INSTANCE), typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("assertEquals", ref.getCorrespondingDeclaration().getName());
        assertEquals(2, ref.getCorrespondingDeclaration().getNoParams());
        assertEquals("java.lang.Object", ref.getCorrespondingDeclaration().getParam(0).getType().asReferenceType().getQualifiedName());
        assertEquals("java.lang.Object", ref.getCorrespondingDeclaration().getParam(1).getType().asReferenceType().getQualifiedName());

    }

/*

    @Test
    public void solveMethodSimpleCase() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<MethodDeclaration> ref = context.solveMethod("foo0", ImmutableList.of(), new JreTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNoParams());
    }

    @Test
    public void solveMethodOverrideCase() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<MethodDeclaration> ref = context.solveMethod("foo1", ImmutableList.of(), new JreTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNoParams());
    }

    @Test
    public void solveMethodInheritedCase() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<MethodDeclaration> ref = context.solveMethod("foo2", ImmutableList.of(), new JreTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("Super", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNoParams());
    }

    @Test
    public void solveMethodWithPrimitiveParameters() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        TypeUsage intType = PrimitiveTypeUsage.INT;

        SymbolReference<MethodDeclaration> ref = context.solveMethod("foo3", ImmutableList.of(intType), new JreTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNoParams());
    }

    @Test
    public void solveMethodWithMoreSpecializedParameter() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        TypeUsage stringType = new TypeUsageOfTypeDeclaration(new ReflectionClassDeclaration(String.class));

        SymbolReference<MethodDeclaration> ref = context.solveMethod("foo4", ImmutableList.of(stringType), new JreTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNoParams());
    }

    @Test(expected = AmbiguityException.class)
    public void solveMethodWithAmbiguosCall() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<MethodDeclaration> ref = context.solveMethod("foo5", ImmutableList.of(new NullTypeUsage()), new JreTypeSolver());
    }

    @Test
    public void solveMethodAsUsageSimpleCase() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo0", ImmutableList.of(), new JreTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageOverrideCase() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo1", ImmutableList.of(), new JreTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageInheritedCase() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo2", ImmutableList.of(), new JreTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("Super", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageWithPrimitiveParameters() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        TypeUsage intType = PrimitiveTypeUsage.INT;

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo3", ImmutableList.of(intType), new JreTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(1, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageWithMoreSpecializedParameter() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        TypeUsage stringType = new TypeUsageOfTypeDeclaration(new ReflectionClassDeclaration(String.class));

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo4", ImmutableList.of(stringType), new JreTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(1, ref.get().getNoParams());
    }

    @Test(expected = AmbiguityException.class)
    public void solveMethodAsUsageWithAmbiguosCall() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo5", ImmutableList.of(new NullTypeUsage()), new JreTypeSolver());
    }*/
}
