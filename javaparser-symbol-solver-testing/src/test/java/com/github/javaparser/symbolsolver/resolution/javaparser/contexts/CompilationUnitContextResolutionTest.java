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
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.CompilationUnitContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.NullType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/**
 * @author Federico Tomassetti
 */
public class CompilationUnitContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    public void getParent() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        Context context = new CompilationUnitContext(cu, typeSolver);

        assertTrue(null == context.getParent());
    }

    @Test
    public void solveExistingGenericType() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        Context context = new CompilationUnitContext(cu, typeSolver);

        Optional<ResolvedType> a = context.solveGenericType("A", new MemoryTypeSolver());
        Optional<ResolvedType> b = context.solveGenericType("B", new MemoryTypeSolver());
        Optional<ResolvedType> c = context.solveGenericType("C", new MemoryTypeSolver());

        assertEquals(false, a.isPresent());
        assertEquals(false, b.isPresent());
        assertEquals(false, c.isPresent());
    }

    @Test
    public void solveUnexistingGenericType() {
        CompilationUnit cu = parseSample("ClassWithTypeVariables");
        Context context = new CompilationUnitContext(cu, typeSolver);

        Optional<ResolvedType> d = context.solveGenericType("D", new MemoryTypeSolver());

        assertEquals(false, d.isPresent());
    }

    @Test
    public void solveSymbolReferringToStaticallyImportedValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("out", typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("java.io.PrintStream", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void solveSymbolReferringToStaticallyImportedUsingAsteriskValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("err", typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("java.io.PrintStream", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void solveSymbolReferringToStaticField() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("java.lang.System.out", new ReflectionTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("java.io.PrintStream", ref.getCorrespondingDeclaration().getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void solveSymbolAsValueReferringToStaticallyImportedValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        Optional<Value> ref = context.solveSymbolAsValue("out", typeSolver);
        assertEquals(true, ref.isPresent());
        assertEquals("java.io.PrintStream", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToStaticallyImportedUsingAsteriskValue() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        Optional<Value> ref = context.solveSymbolAsValue("err", typeSolver);
        assertEquals(true, ref.isPresent());
        assertEquals("java.io.PrintStream", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToStaticField() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("java.lang.System.out", new ReflectionTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("java.io.PrintStream", ref.get().getType().describe());
    }

    @Test
    public void solveTypeInSamePackage() {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        ResolvedReferenceTypeDeclaration otherClass = mock(ResolvedReferenceTypeDeclaration.class);
        when(otherClass.getQualifiedName()).thenReturn("com.foo.OtherClassInSamePackage");
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("com.foo.OtherClassInSamePackage", otherClass);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("OtherClassInSamePackage", memoryTypeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("com.foo.OtherClassInSamePackage", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    public void solveTypeImported() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("Assert", new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        assertEquals(true, ref.isSolved());
        assertEquals("org.junit.Assert", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    public void solveTypeNotImported() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("org.junit.Assume", new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        assertEquals(true, ref.isSolved());
        assertEquals("org.junit.Assume", ref.getCorrespondingDeclaration().getQualifiedName());
    }

    @Test
    public void solveMethodStaticallyImportedWithAsterisk() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitWithImports");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        typeSolver.add(new ReflectionTypeSolver());

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("assertFalse", ImmutableList.of(ResolvedPrimitiveType.BOOLEAN), false, typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("assertFalse", ref.getCorrespondingDeclaration().getName());
        assertEquals(1, ref.getCorrespondingDeclaration().getNumberOfParams());
        assertEquals("boolean", ref.getCorrespondingDeclaration().getParam(0).getType().describe());
        assertEquals(true, ref.getCorrespondingDeclaration().getParam(0).getType().isPrimitive());
    }

    @Test
    public void solveMethodStaticallyImportedWithoutAsterisk() throws ParseException, IOException {
        CompilationUnit cu = parseSample("CompilationUnitSymbols");
        Context context = new CompilationUnitContext(cu, typeSolver);

        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new JarTypeSolver(adaptPath("src/test/resources/junit-4.8.1.jar")));
        typeSolver.add(new ReflectionTypeSolver());

        SymbolReference<ResolvedMethodDeclaration> ref = context.solveMethod("assertEquals", ImmutableList.of(NullType.INSTANCE, NullType.INSTANCE), false, typeSolver);
        assertEquals(true, ref.isSolved());
        assertEquals("assertEquals", ref.getCorrespondingDeclaration().getName());
        assertEquals(2, ref.getCorrespondingDeclaration().getNumberOfParams());
        assertEquals("java.lang.Object", ref.getCorrespondingDeclaration().getParam(0).getType().asReferenceType().getQualifiedName());
        assertEquals("java.lang.Object", ref.getCorrespondingDeclaration().getParam(1).getType().asReferenceType().getQualifiedName());

    }

}
