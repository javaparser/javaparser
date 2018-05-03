package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserConstructorDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ConstructorsResolutionTest extends AbstractResolutionTest {

	@Test
	public void solveNormalConstructor() {
		CompilationUnit cu = parseSample("ConstructorCalls");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testNormalConstructor");
		ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
				                                        .asExpressionStmt().getExpression().asObjectCreationExpr();

		SymbolReference<ResolvedConstructorDeclaration> ref =
				JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
		ConstructorDeclaration actualConstructor =
				((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

		ClassOrInterfaceDeclaration otherClazz = Navigator.demandClass(cu, "OtherClass");
		ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(otherClazz, 0);

		assertEquals(expectedConstructor, actualConstructor);
	}

	@Test
	public void solveInnerClassConstructor() {
		CompilationUnit cu = parseSample("ConstructorCalls");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
		MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerClassConstructor");
		ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(1)
				                                        .asExpressionStmt().getExpression().asObjectCreationExpr();

		SymbolReference<ResolvedConstructorDeclaration> ref =
				JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
		ConstructorDeclaration actualConstructor =
				((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

		ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass");
		ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

		assertEquals(expectedConstructor, actualConstructor);
	}

}
