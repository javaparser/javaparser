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

    @Test
    void testTypesWithSameNameInPackageAndNested_directImplements() throws IOException {
        Path srcRootPath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src2");
        Path extendingTypePath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src2/testresource/A.java");

        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcRootPath);
        StaticJavaParser
                .getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(javaParserTypeSolver));

        CompilationUnit cu = StaticJavaParser.parse(extendingTypePath);
        ClassOrInterfaceDeclaration extendingTypeClass = Navigator.demandClass(cu, "A");

        // Attempt to resolve `DuplicateTypeName` from `class ExtendingType implements **DuplicateTypeName**`
        assumeTrue(extendingTypeClass.getImplementedTypes().size() > 0);
        ClassOrInterfaceType implementedType = extendingTypeClass.getImplementedTypes(0);
        ResolvedReferenceType resolvedImplementedType = implementedType.resolve();

        // Verify qualified name matches the non-nested class in the same package.
        // Note verbose assertions show both the "correct" expected value, and the erroneous value to be avoided.
        String qualifiedName = resolvedImplementedType.getQualifiedName();
        assertEquals("testresource.DuplicateTypeName", qualifiedName, "Error - not resolved to interface in separate file.");
        assertNotEquals("testresource.ExtendingType.DuplicateTypeName", qualifiedName, "Error - resolved to nested class.");
    }

    @Test
    void testTypesWithSameNameInPackageAndNested_directExtends() throws IOException {
        Path srcRootPath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src1");
        Path extendingTypePath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/src1/testresource/A.java");

        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcRootPath);
        StaticJavaParser
                .getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(javaParserTypeSolver));

        CompilationUnit cu = StaticJavaParser.parse(extendingTypePath);
        ClassOrInterfaceDeclaration extendingTypeClass = Navigator.demandClass(cu, "A");

        // Attempt to resolve `DuplicateTypeName` from `class ExtendingType implements **DuplicateTypeName**`
        assumeTrue(extendingTypeClass.getExtendedTypes().size() > 0);
        ClassOrInterfaceType implementedType = extendingTypeClass.getExtendedTypes(0);
        ResolvedReferenceType resolvedImplementedType = implementedType.resolve();

        // Verify qualified name matches the non-nested class in the same package.
        // Note verbose assertions show both the "correct" expected value, and the erroneous value to be avoided.
        String qualifiedName = resolvedImplementedType.getQualifiedName();
        assertEquals("testresource.DuplicateTypeName", qualifiedName, "Error - not resolved to interface in separate file.");
        assertNotEquals("testresource.ExtendingType.DuplicateTypeName", qualifiedName, "Error - resolved to nested class.");
    }
}
