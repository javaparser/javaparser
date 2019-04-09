/*
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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class JavassistTypeParameterDeclarationTest  extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());
    }

    @Test
    void testGetBounds() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.utils.PositionUtils");
        assertTrue(compilationUnit.isClass());

        for (ResolvedMethodDeclaration method : compilationUnit.getDeclaredMethods()) {
            switch (method.getName()) {
                case "sortByBeginPosition":
                    List<ResolvedTypeParameterDeclaration> typeParams =  method.getTypeParameters();
                    assertEquals(1, typeParams.size());
                    assertEquals("T", typeParams.get(0).getName());

                    List<ResolvedTypeParameterDeclaration.Bound> bounds = typeParams.get(0).getBounds();
                    assertEquals(1, bounds.size());
                    assertTrue(bounds.get(0).isExtends());
                    assertEquals("com.github.javaparser.ast.Node", bounds.get(0).getType().describe());
            }
        }
    }

    @Test
    void testGetComplexBounds() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());

        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("javaparser.GenericClass");
        assertTrue(compilationUnit.isClass());

        for (ResolvedMethodDeclaration method : compilationUnit.getDeclaredMethods()) {
            if ("complexGenerics".equals(method.getName())) {
                List<ResolvedTypeParameterDeclaration> typeParams =  method.getTypeParameters();

                assertEquals(1, typeParams.size());
                assertEquals("T", typeParams.get(0).getName());

                List<ResolvedTypeParameterDeclaration.Bound> bounds = typeParams.get(0).getBounds();
                assertEquals(2, bounds.size());
                assertTrue(bounds.get(0).isExtends());
                assertEquals("java.lang.Object", bounds.get(0).getType().describe());
                assertTrue(bounds.get(1).isExtends());
                assertEquals("javaparser.GenericClass.Foo<? extends T>", bounds.get(1).getType().describe());
            }
        }
    }

}
