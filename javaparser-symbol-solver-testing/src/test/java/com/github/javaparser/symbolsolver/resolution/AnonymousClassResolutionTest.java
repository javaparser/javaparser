package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.DefaultConstructorDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.*;

public class AnonymousClassResolutionTest extends AbstractResolutionTest {


	@Test
	public void testAnonymousInterfaceImplementationConstructorResolution() {
		CompilationUnit cu = parseSample("AnonymousClasses");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testInterFoo");
		ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);

		SymbolReference<? extends ResolvedConstructorDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(creationExpr);

		assertTrue(ref.isSolved());

		// How exactly should this situation be handled? A default constructor is called here - but what should the
		// wrapped node be? The interface declaration? There should probably be additional assertions here.
	}

	@Test
	public void testAnonymousInterfaceImplementationMethodResolution() {
		CompilationUnit cu = parseSample("AnonymousClasses");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testInterFoo");
		ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);

		MethodCallExpr methodCallExpr = (MethodCallExpr) method.getBody().get().getStatement(1).getChildNodes().get(0);

		SymbolReference<? extends ResolvedMethodDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(methodCallExpr);
		JavaParserMethodDeclaration mdec = (JavaParserMethodDeclaration) ref.getCorrespondingDeclaration();

		assertTrue(ref.isSolved());
		assertFalse(mdec.isAbstract());
		assertEquals(mdec.getWrappedNode().asMethodDeclaration().getParentNode().get(), creationExpr);
	}

	@Test
	public void testAnonymousClassImplementationConstructorResolution() {
		CompilationUnit cu = parseSample("AnonymousClasses");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testClassFoo");
		ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);

		SymbolReference<? extends ResolvedConstructorDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(creationExpr);

		assertTrue(ref.isSolved());
		assertTrue(ref.getCorrespondingDeclaration() instanceof DefaultConstructorDeclaration);
		assertEquals(((JavaParserClassDeclaration)
				              ((DefaultConstructorDeclaration) ref.getCorrespondingDeclaration())
						              .declaringType())
				             .getWrappedNode(),
		             clazz.findFirst(ClassOrInterfaceDeclaration.class, c -> c.getNameAsString().equals("ClassFoo")).get());
	}

	@Test
	public void testAnonymousClassImplementationMethodResolution() {
		CompilationUnit cu = parseSample("AnonymousClasses");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testClassFoo");
		ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);
		ClassOrInterfaceDeclaration classFooDec =
				clazz.findFirst(ClassOrInterfaceDeclaration.class, c -> c.getNameAsString().equals("ClassFoo")).get();

		MethodCallExpr absFooCall = method.findFirst(MethodCallExpr.class, mce -> mce.getNameAsString().equals("foo")).get();
		MethodCallExpr implFooCall = method.findFirst(MethodCallExpr.class, mce -> mce.getNameAsString().equals("implFoo")).get();

		SymbolReference<? extends ResolvedMethodDeclaration> absRef = JavaParserFacade.get(new ReflectionTypeSolver()).solve(absFooCall);
		SymbolReference<? extends ResolvedMethodDeclaration> implRef = JavaParserFacade.get(new ReflectionTypeSolver()).solve(implFooCall);
		JavaParserMethodDeclaration absDec = (JavaParserMethodDeclaration) absRef.getCorrespondingDeclaration();
		JavaParserMethodDeclaration implDec = (JavaParserMethodDeclaration) implRef.getCorrespondingDeclaration();

		assertTrue(absRef.isSolved());
		assertTrue(implRef.isSolved());
		assertFalse(absDec.isAbstract());
		assertFalse(implDec.isAbstract());
		assertEquals(absDec.getWrappedNode().getParentNode().get(), creationExpr);
		assertEquals(implDec.getWrappedNode().getParentNode().get(), classFooDec);
	}
}
