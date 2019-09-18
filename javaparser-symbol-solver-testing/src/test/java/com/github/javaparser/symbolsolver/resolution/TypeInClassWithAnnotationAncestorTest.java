package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TypeInClassWithAnnotationAncestorTest extends AbstractResolutionTest {

	@Test
	void resolveStringReturnType() {
		CompilationUnit cu = parseSample("ClassWithAnnotationAncestor");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassWithAnnotationAncestor");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testMethod");
		ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver())
				                    .convertToUsage(method.getType(), method.getType());
		assertFalse(type.isTypeVariable());
		assertEquals("java.lang.String", type.describe());
	}
}
