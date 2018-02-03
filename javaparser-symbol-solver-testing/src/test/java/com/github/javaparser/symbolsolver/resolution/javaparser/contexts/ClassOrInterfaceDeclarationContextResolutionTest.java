/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ClassOrInterfaceDeclarationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.CompilationUnitContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.NullType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.Before;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * @author Federico Tomassetti
 */
public class ClassOrInterfaceDeclarationContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    public void getParentForTopClass() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        assertFalse(null == context.getParent());
        assertEquals(new CompilationUnitContext(cu, typeSolver), context.getParent());
    }

    @Test
    public void solveExistingGenericType() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<ResolvedType> a = context.solveGenericType("A", new MemoryTypeSolver());
        Optional<ResolvedType> b = context.solveGenericType("B", new MemoryTypeSolver());
        Optional<ResolvedType> c = context.solveGenericType("C", new MemoryTypeSolver());

        assertEquals(true, a.isPresent());
        assertEquals("A", a.get().describe());
        assertEquals(true, a.get().isTypeVariable());
        assertEquals(true, b.isPresent());
        assertEquals("B", b.get().describe());
        assertEquals(true, b.get().isTypeVariable());
        assertEquals(true, c.isPresent());
        assertEquals("C", c.get().describe());
        assertEquals(true, c.get().isTypeVariable());
    }

    @Test
    public void solveUnexistingGenericType() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<ResolvedType> d = context.solveGenericType("D", new MemoryTypeSolver());

        assertEquals(false, d.isPresent());
    }

    @Test
    public void solveSymbolReferringToDeclaredInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("i", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToDeclaredStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("j", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("long", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("k", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("boolean", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToInterfaceInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("o", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToInheritedStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("m", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("char", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToUnknownElement() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("zzz", new MemoryTypeSolver());
        assertEquals(false, ref.isSolved());
    }

    @Test
    public void solveSymbolAsValueReferringToDeclaredInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("i", new MemoryTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("int", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToDeclaredStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("j", new MemoryTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("long", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("k", new MemoryTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("boolean", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToInterfaceInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        ClassOrInterfaceDeclarationContext context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("o", new MemoryTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("int", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToInheritedStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("m", new MemoryTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("char", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToUnknownElement() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("zzz", new MemoryTypeSolver());
        assertEquals(false, ref.isPresent());
    }

    @Test
    public void solveTypeRefToItself() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("A", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToUnexisting() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Foo", new MemoryTypeSolver());
        assertEquals(false, ref.isSolved());
    }

    @Test
    public void solveTypeRefToObject() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Object", new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToJavaLangObject() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("java.lang.Object", new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("B", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToInternalEnum() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("E", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToInternalOfInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("C", new MemoryTypeSolver());
        assertEquals(false, ref.isSolved());
    }

    @Test
    public void solveTypeRefToAnotherClassInFile() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Super", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToQualifiedInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("A.B", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToQualifiedInternalOfInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("B.C", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveTypeRefToMoreQualifiedInternalOfInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("A.B.C", new MemoryTypeSolver());
        assertEquals(true, ref.isSolved());
    }

    @Test
    public void solveMethodSimpleCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo0", ImmutableList.of(), false, new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    public void solveMethodOverrideCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo1", ImmutableList.of(), false, new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    public void solveMethodInheritedCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo2", ImmutableList.of(), false, new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("Super", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    public void solveMethodWithPrimitiveParameters() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        ResolvedType intType = ResolvedPrimitiveType.INT;

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo3", ImmutableList.of(intType), false, new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    public void solveMethodWithMoreSpecializedParameter() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        ResolvedType stringType = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo4", ImmutableList.of(stringType), false, new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test(expected = MethodAmbiguityException.class)
    public void solveMethodWithAmbiguosCall() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo5", ImmutableList.of(NullType.INSTANCE), false, new ReflectionTypeSolver());
    }

    @Test
    public void solveMethodAsUsageSimpleCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo0", ImmutableList.of(), new ReflectionTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageOverrideCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo1", ImmutableList.of(), new ReflectionTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageInheritedCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo2", ImmutableList.of(), new ReflectionTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("Super", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageWithPrimitiveParameters() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        ResolvedType intType = ResolvedPrimitiveType.INT;

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo3", ImmutableList.of(intType), new ReflectionTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(1, ref.get().getNoParams());
    }

    @Test
    public void solveMethodAsUsageWithMoreSpecializedParameter() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        ResolvedType stringType = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo4", ImmutableList.of(stringType), new ReflectionTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(1, ref.get().getNoParams());
    }

    @Test(expected = MethodAmbiguityException.class)
    public void solveMethodAsUsageWithAmbiguosCall() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo5", ImmutableList.of(NullType.INSTANCE), new ReflectionTypeSolver());
    }
}
