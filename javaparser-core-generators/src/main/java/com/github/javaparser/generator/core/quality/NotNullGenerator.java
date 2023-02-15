/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.generator.core.quality;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.generator.CompilationUnitGenerator;
import com.github.javaparser.quality.NotNull;
import com.github.javaparser.quality.Preconditions;
import com.github.javaparser.utils.SourceRoot;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Generator to process annotations {@link com.github.javaparser.quality.NotNull}.
 */
public class NotNullGenerator extends CompilationUnitGenerator {

	public NotNullGenerator(SourceRoot sourceRoot) {
		super(sourceRoot);
	}

	@Override
	public void generateCompilationUnit(CompilationUnit compilationUnit) {
		compilationUnit.findAll(ConstructorDeclaration.class).forEach(this::generateQualityForConstructor);
		compilationUnit.findAll(MethodDeclaration.class).forEach(this::generateQualityForMethod);
	}

	/**
	 * Generate the pre conditions based on the method parameters.
	 * <br>
	 * If parameters are annotated with {@link com.github.javaparser.quality.NotNull} and a {@code null} is
	 * passed, the method should throw an {@link IllegalArgumentException}.
	 * <br>
	 * If annotated with {@link com.github.javaparser.quality.Nullable}, other annotation or none, nothing should be
	 * changed.
	 *
	 * @param methodDeclaration The method declaration to generate.
	 */
	protected void generateQualityForMethod(MethodDeclaration methodDeclaration) {
		methodDeclaration.getBody().ifPresent(blockStmt ->
				generateQualityForParameter(methodDeclaration, methodDeclaration.getParameters(), blockStmt));
	}

	/**
	 * Generate the pre conditions based on the constructor parameters.
	 * <br>
	 * If parameters are annotated with {@link com.github.javaparser.quality.NotNull} and a {@code null} is
	 * passed, the method should throw an {@link IllegalArgumentException}.
	 * <br>
	 * If annotated with {@link com.github.javaparser.quality.Nullable}, other annotation or none, nothing should be
	 * changed.
	 *
	 * @param constructorDeclaration The constructor declaration to generate.
	 */
	protected void generateQualityForConstructor(ConstructorDeclaration constructorDeclaration) {
		generateQualityForParameter(constructorDeclaration, constructorDeclaration.getParameters(), constructorDeclaration.getBody());
	}

	/**
	 * Generate the pre conditions for the parameters.
	 * <br>
	 * If parameters are annotated with {@link com.github.javaparser.quality.NotNull} and a {@code null} is
	 * passed, the method should throw an {@link IllegalArgumentException}.
	 * <br>
	 * If annotated with {@link com.github.javaparser.quality.Nullable}, other annotation or none, nothing should be
	 * changed.
	 *
	 * @param callableDeclaration 	The declaration where the parameters belong.
	 * @param parameters 			The list of parameters.
	 * @param blockStmt 			The block where the assertions should be added.
	 *
	 * @param <N>					The callable declaration type.
	 */
	protected <N extends CallableDeclaration<?>>
		void generateQualityForParameter(N callableDeclaration, NodeList<Parameter> parameters, BlockStmt blockStmt) {

		List<Statement> assertions = new ArrayList<>();

		for (Parameter parameter : parameters) {
			Optional<AnnotationExpr> nonNullAnnotation = parameter.getAnnotationByClass(NotNull.class);
			if (nonNullAnnotation.isPresent()) {
				assertions.add(createAssertion(parameter));
			}
		}

		insertAssertionsInBlock(callableDeclaration, blockStmt, assertions);
	}

	/**
	 * Create assertion for the parameters.
	 *
	 * @param parameter The parameter to create the assertion.
	 *
	 * @return The assertion to be added to the code.
	 */
	private Statement createAssertion(Parameter parameter) {

		parameter.tryAddImportToParentCompilationUnit(Preconditions.class);
		return StaticJavaParser.parseStatement(
				f("Preconditions.checkNotNull(%s, \"Parameter %s can't be null.\");", parameter.getNameAsString(),
						parameter.getNameAsString())
		);
	}

	/**
	 * Insert the assertions into the block.
	 *
	 * @param callableDeclaration 	The declaration where the parameters belong.
	 * @param blockStmt 			The block where the assertions should be added.
	 * @param assertions 			The list of assertions to be inserted.
	 *
	 * @param <N>					The callable declaration type.
	 */
	private <N extends CallableDeclaration<?>>
		void insertAssertionsInBlock(N callableDeclaration, BlockStmt blockStmt, List<Statement> assertions) {

		// If there's nothing to add, just ignore
		if (assertions.isEmpty())
			return;

		int position = 0;
		NodeList<Statement> statements = blockStmt.getStatements();

		// When the callable is a constructor we must check if is a ExplicitConstructorInvocationStmt.
		if (callableDeclaration.isConstructorDeclaration()) {
			Optional<Statement> optionalFirstStatement = statements.getFirst();
			if (optionalFirstStatement.isPresent()) {

				// Check if the first item is a "super" expr. If it's then we add the assertions after it.
				Statement firstStatement = optionalFirstStatement.get();
				if (firstStatement instanceof ExplicitConstructorInvocationStmt) {
					position = 1;
				}
			}
		}

		// Register assertions
		for (int i = 0 ; i < assertions.size() ; i++) {
			Statement assertion = assertions.get(i);

			Optional<? extends Statement> optOldStmt = getSimilarAssertionInBlock(assertion, blockStmt);

			if (optOldStmt.isPresent()) {
				optOldStmt.get().replace(assertion);
			} else {
				blockStmt.addStatement(position + i, assertion);
			}
		}
	}

	private Optional<? extends Statement> getSimilarAssertionInBlock(Statement assertion, BlockStmt blockStmt) {

		MethodCallExpr assertionCall = assertion.asExpressionStmt().getExpression().asMethodCallExpr();
		List<MethodCallExpr> methodCallExpressions = blockStmt.findAll(MethodCallExpr.class);

		for (MethodCallExpr blockMethodCall : methodCallExpressions) {

			// Check if the method calls name match
			if (
				blockMethodCall.getNameAsExpression().equals(assertionCall.getNameAsExpression()) &&
				blockMethodCall.getScope().equals(assertionCall.getScope()) &&
				blockMethodCall.getArguments().size() == 2 &&
				blockMethodCall.getArguments().get(0).equals(assertionCall.getArgument(0))
			) {
				return blockMethodCall.findAncestor(ExpressionStmt.class);
			}

		}
		// TODO:
		return Optional.empty();
	}

}
