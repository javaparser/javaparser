package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertThrows;

class UnknownMethodsResolutionTest extends AbstractResolutionTest {

	@Test
	void testUnknownMethod1() {
		assertThrows(UnsolvedSymbolException.class, () -> {
		    CompilationUnit cu = parseSample("UnknownMethods");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "UnknownMethods");
		MethodDeclaration method = Navigator.demandMethod(clazz, "test1");
		MethodCallExpr methodCallExpr = method.getBody().get().getStatement(0).asExpressionStmt().getExpression().asMethodCallExpr();
		SymbolReference<ResolvedMethodDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(methodCallExpr);
});
						
}

	@Test
	void testUnknownMethod2() {
		assertThrows(UnsolvedSymbolException.class, () -> {
		    CompilationUnit cu = parseSample("UnknownMethods");
		ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "UnknownMethods");
		MethodDeclaration method = Navigator.demandMethod(clazz, "test2");
		MethodCallExpr methodCallExpr = method.getBody().get().getStatement(1).asExpressionStmt().getExpression().asMethodCallExpr();
		SymbolReference<ResolvedMethodDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(methodCallExpr);
});
						
}
}
