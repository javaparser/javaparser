package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.AbstractTest;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.Value;
import me.tomassetti.symbolsolver.model.declarations.MethodAmbiguityException;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.model.typesolvers.DummyTypeSolver;
import me.tomassetti.symbolsolver.model.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.*;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * @author Federico Tomassetti
 */
public class ClassOrInterfaceDeclarationContextTest extends AbstractTest {

    @Test
    public void getParentForTopClass() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        assertFalse(null == context.getParent());
        assertEquals(new CompilationUnitContext(cu), context.getParent());
    }

    @Test
    public void solveExistingGenericType() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<TypeUsage> a = context.solveGenericType("A", new DummyTypeSolver());
        Optional<TypeUsage> b = context.solveGenericType("B", new DummyTypeSolver());
        Optional<TypeUsage> c = context.solveGenericType("C", new DummyTypeSolver());

        assertEquals(true, a.isPresent());
        assertEquals("A", a.get().getTypeName());
        assertEquals(true, a.get().isTypeVariable());
        assertEquals(true, b.isPresent());
        assertEquals("B", b.get().getTypeName());
        assertEquals(true, b.get().isTypeVariable());
        assertEquals(true, c.isPresent());
        assertEquals("C", c.get().getTypeName());
        assertEquals(true, c.get().isTypeVariable());
    }

    @Test
    public void solveUnexistingGenericType() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<TypeUsage> d = context.solveGenericType("D", new DummyTypeSolver());

        assertEquals(false, d.isPresent());
    }

    @Test
    public void solveSymbolReferringToDeclaredInstanceField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("i", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType(new DummyTypeSolver()).getTypeName());
    }

    @Test
    public void solveSymbolReferringToDeclaredStaticField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("j", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("long", ref.getCorrespondingDeclaration().getType(new DummyTypeSolver()).getTypeName());
    }

    @Test
    public void solveSymbolReferringToInehritedInstanceField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("k", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("boolean", ref.getCorrespondingDeclaration().getType(new DummyTypeSolver()).getTypeName());
    }

    @Test
    public void solveSymbolReferringToInheritedStaticField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("m", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("char", ref.getCorrespondingDeclaration().getType(new DummyTypeSolver()).getTypeName());
    }

    @Test
    public void solveSymbolReferringToUnknownElement() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("zzz", new DummyTypeSolver());
        assertEquals(false, ref.isSolved());
    }

    @Test
    public void solveSymbolAsValueReferringToDeclaredInstanceField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<Value> ref = context.solveSymbolAsValue("i", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("int", ref.get().getUsage().getTypeName());
    }

    @Test
    public void solveSymbolAsValueReferringToDeclaredStaticField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<Value> ref = context.solveSymbolAsValue("j", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("long", ref.get().getUsage().getTypeName());
    }

    @Test
    public void solveSymbolAsValueReferringToInehritedInstanceField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<Value> ref = context.solveSymbolAsValue("k", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("boolean", ref.get().getUsage().getTypeName());
    }

    @Test
    public void solveSymbolAsValueReferringToInheritedStaticField() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<Value> ref = context.solveSymbolAsValue("m", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("char", ref.get().getUsage().getTypeName());
    }

    @Test
    public void solveSymbolAsValueReferringToUnknownElement() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<Value> ref = context.solveSymbolAsValue("zzz", new DummyTypeSolver());
        assertEquals(false, ref.isPresent());
    }

    @Test
    public void solveTypeRefToItself() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("A", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToUnexisting() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("Foo", new DummyTypeSolver());
        assertEquals(false, ref.isSolved());
    }

    @Test
    public void solveTypeRefToObject() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("Object", new JreTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToJavaLangObject() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("java.lang.Object", new JreTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToInternalClass() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("B", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToInternalEnum() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("E", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToInternalOfInternalClass() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("C", new DummyTypeSolver());
        assertEquals(false, ref.isSolved());
    }

    @Test
    public void solveTypeRefToAnotherClassInFile() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("Super", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToQualifiedInternalClass() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("A.B", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToQualifiedInternalOfInternalClass() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("B.C", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToMoreQualifiedInternalOfInternalClass() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        SymbolReference<TypeDeclaration> ref = context.solveType("A.B.C", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
    }

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

    @Test(expected = MethodAmbiguityException.class)
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

    @Test(expected = MethodAmbiguityException.class)
    public void solveMethodAsUsageWithAmbiguosCall() throws ParseException {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo5", ImmutableList.of(new NullTypeUsage()), new JreTypeSolver());
    }
}
