package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TypeResolutionWithSameNameTest extends AbstractResolutionTest {

	@Test
	void testTypesWithSameNameInPackageAndNested() throws IOException {
		Path srcPath = adaptPath("src/test/resources/TypeResolutionWithSameNameTest");
		JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(srcPath);
		StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(
				new CombinedTypeSolver(new ReflectionTypeSolver(), javaParserTypeSolver)));

		CompilationUnit cu = StaticJavaParser.parse(
				adaptPath("src/test/resources/TypeResolutionWithSameNameTest/testresource/ExtendingType.java"));
		ClassOrInterfaceDeclaration extendingType = Navigator.demandClass(cu, "ExtendingType");
		ClassOrInterfaceType implementedType = extendingType.getImplementedTypes(0);

		ResolvedReferenceType resolvedImplementedType = implementedType.resolve();

		assertEquals("testresource.DuplicateTypeName", resolvedImplementedType.getQualifiedName());
	}
}
