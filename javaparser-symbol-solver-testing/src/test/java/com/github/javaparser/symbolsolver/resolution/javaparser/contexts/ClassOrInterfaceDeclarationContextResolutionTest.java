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
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * @author Federico Tomassetti
 */
class ClassOrInterfaceDeclarationContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    void getParentForTopClass() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        assertFalse(null == context.getParent());
        assertEquals(new CompilationUnitContext(cu, typeSolver), context.getParent());
    }

    @Test
    void solveExistingGenericType() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<ResolvedType> a = context.solveGenericType("A");
        Optional<ResolvedType> b = context.solveGenericType("B");
        Optional<ResolvedType> c = context.solveGenericType("C");
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
    void solveUnexistingGenericType() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<ResolvedType> d = context.solveGenericType("D");

        assertEquals(false, d.isPresent());
    }

    @Test
    void solveSymbolReferringToDeclaredInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("i");
        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToDeclaredStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("j");
        assertEquals(true, ref.isSolved());
        assertEquals("long", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("k");
        assertEquals(true, ref.isSolved());
        assertEquals("boolean", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToInterfaceInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("o");
        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToInheritedStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("m");
        assertEquals(true, ref.isSolved());
        assertEquals("char", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToUnknownElement() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("zzz");
        assertEquals(false, ref.isSolved());
    }

    @Test
    void solveSymbolAsValueReferringToDeclaredInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("i");
        assertEquals(true, ref.isPresent());
        assertEquals("int", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToDeclaredStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("j");
        assertEquals(true, ref.isPresent());
        assertEquals("long", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("k");
        assertEquals(true, ref.isPresent());
        assertEquals("boolean", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToInterfaceInheritedInstanceField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        ClassOrInterfaceDeclarationContext context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("o");
        assertEquals(true, ref.isPresent());
        assertEquals("int", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToInheritedStaticField() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("m");
        assertEquals(true, ref.isPresent());
        assertEquals("char", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToUnknownElement() {
        CompilationUnit cu = parseSample("ClassWithSymbols");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("zzz");
        assertEquals(false, ref.isPresent());
    }

    @Test
    void solveTypeRefToItself() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("A");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToUnexisting() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Foo");
        assertEquals(false, ref.isSolved());
    }

    @Test
    void solveTypeRefToObject() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Object");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToJavaLangObject() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("java.lang.Object");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("B");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToInternalEnum() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("E");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToInternalOfInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("C");
        assertEquals(false, ref.isSolved());
    }

    @Test
    void solveTypeRefToAnotherClassInFile() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Super");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToQualifiedInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("A.B");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToQualifiedInternalOfInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("B.C");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToMoreQualifiedInternalOfInternalClass() {
        CompilationUnit cu = parseSample("ClassWithTypes");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("A.B.C");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveMethodSimpleCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo0", ImmutableList.of(), false);
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveMethodOverrideCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo1", ImmutableList.of(), false);
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveMethodInheritedCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo2", ImmutableList.of(), false);
        assertEquals(true, ref.isSolved());
        assertEquals("Super", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveMethodWithPrimitiveParameters() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        ResolvedType intType = ResolvedPrimitiveType.INT;

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo3", ImmutableList.of(intType), false);
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveMethodWithMoreSpecializedParameter() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);

        ResolvedType stringType = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo4", ImmutableList.of(stringType), false);
        assertEquals(true, ref.isSolved());
        assertEquals("A", ref.getCorrespondingDeclaration().declaringType().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveMethodWithAmbiguosCall() {
        assertThrows(MethodAmbiguityException.class, () -> {
            CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, typeSolver);
        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("foo5", ImmutableList.of(NullType.INSTANCE), false);
    });
                
}

    @Test
    void solveMethodAsUsageSimpleCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration,
                                                                 new ReflectionTypeSolver());

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo0", ImmutableList.of());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    void solveMethodAsUsageOverrideCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration,
                                                                 new ReflectionTypeSolver());

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo1", ImmutableList.of());
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    void solveMethodAsUsageInheritedCase() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration,
                                                                 new ReflectionTypeSolver());

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo2", ImmutableList.of());
        assertEquals(true, ref.isPresent());
        assertEquals("Super", ref.get().declaringType().getName());
        assertEquals(0, ref.get().getNoParams());
    }

    @Test
    void solveMethodAsUsageWithPrimitiveParameters() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration,
                                                                 new ReflectionTypeSolver());

        ResolvedType intType = ResolvedPrimitiveType.INT;

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo3", ImmutableList.of(intType));
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(1, ref.get().getNoParams());
    }

    @Test
    void solveMethodAsUsageWithMoreSpecializedParameter() {
        CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration,
                                                                 new ReflectionTypeSolver());

        ResolvedType stringType = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo4", ImmutableList.of(stringType));
        assertEquals(true, ref.isPresent());
        assertEquals("A", ref.get().declaringType().getName());
        assertEquals(1, ref.get().getNoParams());
    }

    @Test
    void solveMethodAsUsageWithAmbiguosCall() {
        assertThrows(MethodAmbiguityException.class, () -> {
            CompilationUnit cu = parseSample("ClassWithMethods");
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClass(cu, "A");
        Context context = new ClassOrInterfaceDeclarationContext(classOrInterfaceDeclaration, new ReflectionTypeSolver());
        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo5", ImmutableList.of(NullType.INSTANCE));
    });
                
}
}