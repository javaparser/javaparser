/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.bdd.steps;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.util.List;
import java.util.Map;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.bdd.steps.SharedSteps.getMemberByTypeAndPosition;
import static com.github.javaparser.bdd.steps.SharedSteps.getMethodByPositionAndClassPosition;
import static java.lang.String.format;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsNull.notNullValue;
import static org.junit.Assert.*;

public class ParsingSteps {

    private Map<String, Object> state;

    public ParsingSteps(Map<String, Object> state) {
        this.state = state;
    }

    private String sourceUnderTest;

    /*
     * Given steps
     */

    @Given("the class:$classSrc")
    public void givenTheClass(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }


    /*
     * When steps
     */

    @When("I take the ArrayCreationExpr")
    public void iTakeTheArrayCreationExpr() {
        setSelectedNodeFromCompilationUnit(ArrayCreationExpr.class);
    }

    @When("I take the PackageDeclaration")
    public void iTakeThePackageDeclaration() {
        setSelectedNodeFromCompilationUnit(PackageDeclaration.class);
    }

    @When("I take the ObjectCreationExpr")
    public void iTakeTheObjectCreationExpr() throws ClassNotFoundException {
        setSelectedNodeFromCompilationUnit(ObjectCreationExpr.class);
    }

    /*
     * Then steps
     */

    @Then("constructor $constructorPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenTheConstructorDeclarationAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration) compilationUnit.getType(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration) clazz.getMember(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(), is(expectedString));
    }

    @Then("constructor $constructorPosition in class $classPosition declaration short form as a String is \"$expectedString\"")
    public void thenConstructorInClassDeclarationShortFormAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration) compilationUnit.getType(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration) clazz.getMember(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(false, false), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenMethod1InClass1DeclarationAsAStringIs(int methodPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration) compilationUnit.getType(classPosition - 1);
        MethodDeclaration method = (MethodDeclaration) clazz.getMember(methodPosition - 1);
        assertThat(method.getDeclarationAsString(), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String short form is \"$expectedString\"")
    public void thenMethodInClassDeclarationAsAStringShortFormIs(int methodPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration) compilationUnit.getType(classPosition - 1);
        MethodDeclaration method = (MethodDeclaration) clazz.getMember(methodPosition - 1);
        assertThat(method.getDeclarationAsString(false, false), is(expectedString));
    }

    @Then("field $fieldPosition in class $classPosition contains annotation $annotationPosition value is \"$expectedValue\"")
    public void thenFieldInClassContainsAnnotationValueIs(int fieldPosition, int classPosition, int annotationPosition, String expectedValue) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");

        TypeDeclaration<?> classUnderTest = compilationUnit.getType(classPosition - 1);
        FieldDeclaration fieldUnderTest = getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        AnnotationExpr annotationUnderTest = fieldUnderTest.getAnnotation(annotationPosition - 1);
        assertThat(annotationUnderTest.getChildNodes().get(1).toString(), is(expectedValue));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition is called $expectedName")
    public void thenLambdaInClassIsCalled(int statementPosition, int methodPosition, int classPosition, String expectedName) {
        Statement statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        VariableDeclarationExpr expression = (VariableDeclarationExpr) ((ExpressionStmt) statement).getExpression();
        VariableDeclarator variableDeclarator = expression.getVariable(0);
        assertThat(variableDeclarator.getNameAsString(), is(expectedName));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition body is \"$expectedBody\"")
    public void thenLambdaInStatementInMethodInClassBody(int statementPosition, int methodPosition, int classPosition,
                                                         String expectedBody) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        assertThat(lambdaExpr.getBody().toString(), is(expectedBody));
    }

    @Then("lambda in method call in statement $statementPosition in method $methodPosition in class $classPosition body is \"$expectedBody\"")
    public void thenLambdaInMethodCallInStatementInMethodInClassBody(int statementPosition, int methodPosition, int classPosition,
                                                                     String expectedBody) {
        ExpressionStmt statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition).asExpressionStmt();
        VariableDeclarationExpr variableDeclarationExpr = statement.getExpression().asVariableDeclarationExpr();
        VariableDeclarator variableDeclarator = variableDeclarationExpr.getVariable(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) variableDeclarator.getInitializer().orElse(null);
        CastExpr castExpr = methodCallExpr.getArgument(0).asCastExpr();
        LambdaExpr lambdaExpr = castExpr.getExpression().asLambdaExpr();
        assertThat(lambdaExpr.getBody().toString(), is(expectedBody));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition block statement is null")
    public void thenLambdaInStatementInMethodInClassBlockStatementIsNull(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        BlockStmt blockStmt = lambdaExpr.getBody().asBlockStmt();
        assertEquals(true, blockStmt.getStatements().isEmpty());
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition has parameters with non-null type")
    public void thenLambdaInStatementInMethodInClassHasParametersWithNonNullType(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        for (Parameter parameter : lambdaExpr.getParameters()) {
            assertThat(parameter.getType(), is(notNullValue()));
        }
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition block statement is \"$expectedBody\"")
    public void thenLambdaInStatementInMethodInClassBlockStatement(int statementPosition, int methodPosition, int classPosition,
                                                                   String expectedBody) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        BlockStmt blockStmt = lambdaExpr.getBody().asBlockStmt();
        Statement lambdaStmt = blockStmt.getStatement(0);
        assertThat(lambdaStmt.toString(), is(expectedBody));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition is parent of contained body")
    public void thenLambdaInStatementInMethodInClassIsParentOfContainedBody(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        Statement body = lambdaExpr.getBody();
        assertThat(body.getParentNode().get(), is(lambdaExpr));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition is parent of contained parameter")
    public void thenLambdaInStatementInMethodInClassIsParentOfContainedParameter(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        Parameter parameter = lambdaExpr.getParameter(0);
        assertThat(parameter.getParentNode().get(), is(lambdaExpr));
    }

    @Then("method reference in statement $statementPosition in method $methodPosition in class $classPosition scope is $expectedName")
    public void thenMethodReferenceInStatementInMethodInClassIsScope(int statementPosition, int methodPosition,
                                                                     int classPosition, String expectedName) {
        ExpressionStmt statementUnderTest = getStatementInMethodInClass(statementPosition, methodPosition, classPosition).asExpressionStmt();
        assertEquals(1, statementUnderTest.findAll(MethodReferenceExpr.class).size());
        MethodReferenceExpr methodReferenceUnderTest = statementUnderTest.findFirst(MethodReferenceExpr.class).get();
        assertThat(methodReferenceUnderTest.getScope().toString(), is(expectedName));
    }

    @Then("method reference in statement $statementPosition in method $methodPosition in class $classPosition identifier is $expectedName")
    public void thenMethodReferenceInStatementInMethodInClassIdentifierIsCompareByAge(int statementPosition, int methodPosition,
                                                                                      int classPosition, String expectedName) {
        Statement statementUnderTest = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        assertEquals(1, statementUnderTest.findAll(MethodReferenceExpr.class).size());
        MethodReferenceExpr methodReferenceUnderTest = statementUnderTest.findFirst(MethodReferenceExpr.class).get();
        assertThat(methodReferenceUnderTest.getIdentifier(), is(expectedName));
    }

    @Then("method $methodPosition class $classPosition is a default method")
    public void thenMethodClassIsADefaultMethod(int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration methodUnderTest = getMethodByPositionAndClassPosition(compilationUnit,
                methodPosition, classPosition);
        assertThat(methodUnderTest.isDefault(), is(true));
    }

    @Then("method $methodPosition class $classPosition is not a default method")
    public void thenMethodClassIsNotADefaultMethod(int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration methodUnderTest = getMethodByPositionAndClassPosition(compilationUnit,
                methodPosition, classPosition);
        assertThat(methodUnderTest.isDefault(), is(false));
    }

    private Statement getStatementInMethodInClass(int statementPosition, int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        return method.getBody().get().getStatement(statementPosition - 1);
    }

    private LambdaExpr getLambdaExprInStatementInMethodInClass(int statementPosition, int methodPosition, int classPosition) {
        Statement statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        VariableDeclarationExpr expression = ((ExpressionStmt) statement).getExpression().asVariableDeclarationExpr();
        VariableDeclarator variableDeclarator = expression.getVariable(0);
        return (LambdaExpr) variableDeclarator.getInitializer().orElse(null);
    }

    @Then("all nodes refer to their parent")
    public void allNodesReferToTheirParent() {
        assertAllNodesOfTheCompilationUnitHaveTheirParentSet("cu1");
    }

    @Then("all nodes of the second compilation unit refer to their parent")
    public void thenAllNodesOfTheSecondCompilationUnitReferToTheirParent() {
        assertAllNodesOfTheCompilationUnitHaveTheirParentSet("cu2");
    }

    private void assertAllNodesOfTheCompilationUnitHaveTheirParentSet(String stateKey) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get(stateKey);
        ExistenceOfParentNodeVerifier parentVerifier = new ExistenceOfParentNodeVerifier();
        parentVerifier.verify(compilationUnit);
    }

    @Then("ThenExpr in the conditional expression of the statement $statementPosition in method $methodPosition in class $classPosition is LambdaExpr")
    public void thenLambdaInConditionalExpressionInMethodInClassIsParentOfContainedParameter(int statementPosition, int methodPosition, int classPosition) {
        ReturnStmt returnStmt = getStatementInMethodInClass(statementPosition, methodPosition, classPosition).asReturnStmt();
        ConditionalExpr conditionalExpr = (ConditionalExpr) returnStmt.getExpression().orElse(null);
        assertThat(conditionalExpr.getElseExpr().getClass().getName(), is(LambdaExpr.class.getName()));
    }

    @Then("the begin line is $line")
    public void thenTheBeginLineIs(int line) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(line, node.getBegin().get().line);
    }

    @Then("the begin column is $column")
    public void thenTheBeginColumnIs(int column) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(column, node.getBegin().get().column);
    }

    @Then("the end line is $line")
    public void thenTheEndLineIs(int line) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(line, node.getEnd().get().line);
    }

    @Then("the end column is $column")
    public void thenTheEndColumnIs(int column) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(column, node.getEnd().get().column);
    }

    @Then("no errors are reported")
    public void thenNoErrorsAreReported() {
        // this is present just for readability in the scenario specification
        // if the code is not parsed then exceptions are thrown before reaching this step
    }

    @Then("the package name is $package")
    public void thenThePackageNameIs(String expected) {
        PackageDeclaration node = (PackageDeclaration) state.get("selectedNode");
        assertEquals(expected, node.getNameAsString());
        assertEquals(expected, node.getName().toString());
    }

    @Then("the type's diamond operator flag should be $expectedValue")
    public void thenTheUsesDiamondOperatorShouldBeBooleanAsString(boolean expectedValue) {
        ObjectCreationExpr expr = (ObjectCreationExpr) state.get("selectedNode");
        assertEquals(expectedValue, expr.getType().isUsingDiamondOperator());
    }

    @Then("the Java parser cannot parse it because of an error")
    public void javaParserCannotParseBecauseOfLexicalErrors() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider(sourceUnderTest));
        if (result.isSuccessful()) {
            fail("Lexical error expected");
        }
    }

    @Then("the assignExpr produced doesn't have a null target")
    public void thenTheAssignExprProducedDoesntHaveANullTarget() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration classDeclaration = compilationUnit.getType(0).asClassOrInterfaceDeclaration();
        ConstructorDeclaration ctor = classDeclaration.getMember(1).asConstructorDeclaration();
        ExpressionStmt assignStmt = ctor.getBody().getStatement(0).asExpressionStmt();
        AssignExpr assignExpr = assignStmt.getExpression().asAssignExpr();
        assertNotNull(assignExpr.getTarget());
        assertEquals(NameExpr.class, assignExpr.getTarget().getClass());
        assertEquals(assignExpr.getTarget().asNameExpr().getNameAsString(), "mString");
    }

    private void setSelectedNodeFromCompilationUnit(Class<? extends Node> nodeType) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        List<? extends Node> nodes = compilationUnit.findAll(nodeType);
        if (nodes.size() != 1) {
            throw new RuntimeException(format("Exactly one %s expected", nodeType.getSimpleName()));
        }
        state.put("selectedNode", nodes.get(0));
    }
}
