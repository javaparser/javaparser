package com.github.javaparser.symbolsolver.resolution.logic;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class FunctionalInterfaceLogicTest extends AbstractSymbolResolutionTest {

	private TypeSolver typeSolver;

	@BeforeEach
	void setup() throws Exception {
        CombinedTypeSolver combinedtypeSolver = new CombinedTypeSolver();
        combinedtypeSolver.add(new ReflectionTypeSolver());
        typeSolver = combinedtypeSolver;
    }

	@Test
	void simleExampleOfFunctionnalInterface() {
		String code = "interface Runnable {\n"
				+ "    void run();\n"
				+ "}";

		CompilationUnit cu = StaticJavaParser.parse(code);
		ClassOrInterfaceDeclaration classOrInterfaceDecl = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
		ResolvedInterfaceDeclaration resolvedDecl = new JavaParserInterfaceDeclaration(classOrInterfaceDecl, typeSolver);
		Optional<MethodUsage>  methodUsage = FunctionalInterfaceLogic.getFunctionalMethod(resolvedDecl);
		assertTrue(methodUsage.isPresent());
	}

	@Test
	void notFunctionalBecauseItDeclaresNothingWhichIsNotAlreadyAMemberOfObject() {
		String code = "interface NonFunc {\n"
				+ "    boolean equals(Object obj);\n"
				+ "}";

		CompilationUnit cu = StaticJavaParser.parse(code);
		ClassOrInterfaceDeclaration classOrInterfaceDecl = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
		ResolvedInterfaceDeclaration resolvedDecl = new JavaParserInterfaceDeclaration(classOrInterfaceDecl, typeSolver);
		Optional<MethodUsage>  methodUsage = FunctionalInterfaceLogic.getFunctionalMethod(resolvedDecl);
		assertFalse(methodUsage.isPresent());
	}

	@Test
	void subinterfaceCanBeFunctionalByDclaringAnAbstractMethodWhichIsNotAMemberOfObject() {
		String code = "interface NonFunc {\n"
				+ "    boolean equals(Object obj);\n"
				+ "}\n"
				+ "interface Func extends NonFunc {\n"
				+ "    int compare(String o1, String o2);\n"
				+ "}";

		CompilationUnit cu = StaticJavaParser.parse(code);
		ClassOrInterfaceDeclaration classOrInterfaceDecl = Navigator.demandInterface(cu, "Func");
		ResolvedInterfaceDeclaration resolvedDecl = new JavaParserInterfaceDeclaration(classOrInterfaceDecl, typeSolver);
		Optional<MethodUsage>  methodUsage = FunctionalInterfaceLogic.getFunctionalMethod(resolvedDecl);
		assertTrue(methodUsage.isPresent());
	}

	@Test
	void  isFunctionalBecauseItHasOneAbstractNonObjectMethod() {
		String code = "interface Comparator<T> {\n"
				+ "    boolean equals(Object obj);\n"
				+ "    int compare(T o1, T o2);\n"
				+ "}";

		CompilationUnit cu = StaticJavaParser.parse(code);
		ClassOrInterfaceDeclaration classOrInterfaceDecl = Navigator.demandInterface(cu, "Comparator");
		ResolvedInterfaceDeclaration resolvedDecl = new JavaParserInterfaceDeclaration(classOrInterfaceDecl, typeSolver);
		Optional<MethodUsage>  methodUsage = FunctionalInterfaceLogic.getFunctionalMethod(resolvedDecl);
		assertTrue(methodUsage.isPresent());
	}

	@Test
	void  isNotFunctionalBecauseItDeclaresTwoAbstractMethodsWhichAreNotPublicMembersOfObject() {
		String code = "interface Foo {\n"
				+ "    int m();\n"
				+ "    Object clone();\n"
				+ "}";

		CompilationUnit cu = StaticJavaParser.parse(code);
		ClassOrInterfaceDeclaration classOrInterfaceDecl = Navigator.demandInterface(cu, "Foo");
		ResolvedInterfaceDeclaration resolvedDecl = new JavaParserInterfaceDeclaration(classOrInterfaceDecl, typeSolver);
		Optional<MethodUsage>  methodUsage = FunctionalInterfaceLogic.getFunctionalMethod(resolvedDecl);
		assertFalse(methodUsage.isPresent());
	}

}
