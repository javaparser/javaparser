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

public class TypeResolutionWithSameNameTest extends AbstractResolutionTest {

    @Test
    void testTypesWithSameNameInPackageAndNested() throws IOException {
        Path srcRootPath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest");
        Path extendingTypePath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest/testresource/A.java");

        JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcRootPath);
        StaticJavaParser
                .getConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(javaParserTypeSolver));

        CompilationUnit cu = StaticJavaParser.parse(extendingTypePath);
        ClassOrInterfaceDeclaration extendingTypeClass = Navigator.demandClass(cu, "A");

        // Attempt to resolve `DuplicateTypeName` from `class ExtendingType implements **DuplicateTypeName**`
        ClassOrInterfaceType implementedType = extendingTypeClass.getImplementedTypes(0);
        ResolvedReferenceType resolvedImplementedType = implementedType.resolve();

        // Verify qualified name matches the non-nested class in the same package.
        // Note verbose assertions show both the "correct" expected value, and the erroneous value to be avoided.
        String qualifiedName = resolvedImplementedType.getQualifiedName();
        assertEquals("testresource.DuplicateTypeName", qualifiedName, "Error - not resolved to interface in separate file.");
        assertNotEquals("testresource.ExtendingType.DuplicateTypeName", qualifiedName, "Error - resolved to nested class.");
    }
}
