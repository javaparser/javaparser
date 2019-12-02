/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

public class TypeResolutionWithSameNameTest extends AbstractResolutionTest {


    /*
     * abstract class extends_duplicate.DuplicateTypeName
     * class extends_duplicate.A extends extends_duplicate.DuplicateTypeName
     * class extends_duplicate.A.DuplicateTypeName extends extends_duplicate.A
     */
    @Test
    void testTypesWithSameNameInPackageAndNested_directExtends() throws IOException {
        Path srcRootPath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src1");
        Path extendsTypePath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src1/extends_duplicate/A.java");

        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcRootPath);
        StaticJavaParser
                .getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(javaParserTypeSolver));

        CompilationUnit cu = StaticJavaParser.parse(extendsTypePath);
        ClassOrInterfaceDeclaration extendingTypeClass = Navigator.demandClass(cu, "A");

        // Attempt to resolve `DuplicateTypeName` from `class ExtendingType extends **DuplicateTypeName**`
        assumeTrue(extendingTypeClass.getExtendedTypes().size() > 0);
        ClassOrInterfaceType extendedType = extendingTypeClass.getExtendedTypes(0);
        ResolvedReferenceType resolvedExtendedType = extendedType.resolve();

        // Verify qualified name matches the non-nested class in the same package.
        // Note verbose assertions show both the "correct" expected value, and the erroneous value to be avoided.
        String qualifiedName = resolvedExtendedType.getQualifiedName();
        assertEquals("extends_duplicate.DuplicateTypeName", qualifiedName, "Error - not resolved to interface in separate file.");
        assertNotEquals("extends_duplicate.A.DuplicateTypeName", qualifiedName, "Error - resolved to nested class.");
    }


    /*
     * interface implements_duplicate.DuplicateTypeName
     * class implements_duplicate.class A implements implements_duplicate.DuplicateTypeName
     * class implements_duplicate.A.DuplicateTypeName extends implements_duplicate.A
     */
    @Test
    void testTypesWithSameNameInPackageAndNested_directImplements() throws IOException {
        Path srcRootPath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src2");
        Path implementingTypePath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src2/implements_duplicate/A.java");

        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcRootPath);
        StaticJavaParser
                .getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(javaParserTypeSolver));

        CompilationUnit cu = StaticJavaParser.parse(implementingTypePath);
        ClassOrInterfaceDeclaration implementingTypeClass = Navigator.demandClass(cu, "A");

        // Attempt to resolve `DuplicateTypeName` from `class ImplementingType implements **DuplicateTypeName**`
        assumeTrue(implementingTypeClass.getImplementedTypes().size() > 0);
        ClassOrInterfaceType implementedType = implementingTypeClass.getImplementedTypes(0);
        ResolvedReferenceType resolvedImplementedType = implementedType.resolve();

        // Verify qualified name matches the non-nested class in the same package.
        // Note verbose assertions show both the "correct" expected value, and the erroneous value to be avoided.
        String qualifiedName = resolvedImplementedType.getQualifiedName();
        assertEquals("implements_duplicate.DuplicateTypeName", qualifiedName, "Error - not resolved to interface in separate file.");
        assertNotEquals("implements_duplicate.A.DuplicateTypeName", qualifiedName, "Error - resolved to nested class.");
    }


}
