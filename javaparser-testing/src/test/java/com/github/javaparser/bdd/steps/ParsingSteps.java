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

import static com.github.javaparser.bdd.steps.SharedSteps.getMemberByTypeAndPosition;
import static com.github.javaparser.bdd.steps.SharedSteps.getMethodByPositionAndClassPosition;
import static java.lang.String.format;
import static org.hamcrest.Matchers.empty;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsNull.notNullValue;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.fail;

import java.io.StringReader;
import java.util.List;
import java.util.Map;

import com.github.javaparser.ParseProblemException;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.TokenMgrException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;

public class ParsingSteps {

    private Map<String, Object> state;

    public ParsingSteps(Map<String, Object> state){
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
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(), is(expectedString));
    }

    @Then("constructor $constructorPosition in class $classPosition declaration short form as a String is \"$expectedString\"")
    public void thenConstructorInClassDeclarationShortFormAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(false,false), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenMethod1InClass1DeclarationAsAStringIs(int methodPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition -1);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(methodPosition -1);
        assertThat(method.getDeclarationAsString(), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String short form is \"$expectedString\"")
    public void thenMethodInClassDeclarationAsAStringShortFormIs(int methodPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(methodPosition -1);
        assertThat(method.getDeclarationAsString(false, false), is(expectedString));
    }

    @Then("field $fieldPosition in class $classPosition contains annotation $annotationPosition value is \"$expectedValue\"")
    public void thenFieldInClassContainsAnnotationValueIs(int fieldPosition, int classPosition, int annotationPosition, String expectedValue) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");

		TypeDeclaration<?> classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        AnnotationExpr annotationUnderTest = fieldUnderTest.getAnnotations().get(annotationPosition - 1);
        assertThat(annotationUnderTest.getChildrenNodes().get(1).toString(), is(expectedValue));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition is called $expectedName")
    public void thenLambdaInClassIsCalled(int statementPosition, int methodPosition, int classPosition, String expectedName) {
        Statement statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        VariableDeclarator variableDeclarator = (VariableDeclarator)statement.getChildrenNodes().get(0).getChildrenNodes().get(1);
        assertThat(variableDeclarator.getId().getName(), is(expectedName));
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
        ExpressionStmt statement = (ExpressionStmt) getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) statement.getExpression();
        VariableDeclarator variableDeclarator = variableDeclarationExpr.getVars().get(0);
        MethodCallExpr methodCallExpr = (MethodCallExpr) variableDeclarator.getInit();
        CastExpr castExpr = (CastExpr) methodCallExpr.getArgs().get(0);
        LambdaExpr lambdaExpr = (LambdaExpr) castExpr.getExpr();
        assertThat(lambdaExpr.getBody().toString(), is(expectedBody));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition block statement is null")
    public void thenLambdaInStatementInMethodInClassBlockStatementIsNull(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        BlockStmt blockStmt = (BlockStmt) lambdaExpr.getBody();
        assertThat(blockStmt.getStmts(), is(empty()));
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
        BlockStmt blockStmt = (BlockStmt) lambdaExpr.getBody();
        Statement lambdaStmt = blockStmt.getStmts().get(0);
        assertThat(lambdaStmt.toString(), is(expectedBody));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition is parent of contained body")
    public void thenLambdaInStatementInMethodInClassIsParentOfContainedBody(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        Statement body = lambdaExpr.getBody();
        assertThat(body.getParentNode(), is((Node) lambdaExpr));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition is parent of contained parameter")
    public void thenLambdaInStatementInMethodInClassIsParentOfContainedParameter(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        Parameter parameter = lambdaExpr.getParameters().get(0);
        assertThat(parameter.getParentNode(), is((Node) lambdaExpr));
    }

    @Then("method reference in statement $statementPosition in method $methodPosition in class $classPosition scope is $expectedName")
    public void thenMethodReferenceInStatementInMethodInClassIsScope(int statementPosition, int methodPosition,
                                                                     int classPosition, String expectedName) {
        ExpressionStmt statementUnderTest = (ExpressionStmt)getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        assertEquals(1, statementUnderTest.getNodesByType(MethodReferenceExpr.class).size());
        MethodReferenceExpr methodReferenceUnderTest = statementUnderTest.getNodesByType(MethodReferenceExpr.class).get(0);
        assertThat(methodReferenceUnderTest.getScope().toString(), is(expectedName));
    }

    @Then("method reference in statement $statementPosition in method $methodPosition in class $classPosition identifier is $expectedName")
    public void thenMethodReferenceInStatementInMethodInClassIdentifierIsCompareByAge(int statementPosition, int methodPosition,
                                                                                      int classPosition, String expectedName) {
        Statement statementUnderTest = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        assertEquals(1, statementUnderTest.getNodesByType(MethodReferenceExpr.class).size());
        MethodReferenceExpr methodReferenceUnderTest = statementUnderTest.getNodesByType(MethodReferenceExpr.class).get(0);
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
        return method.getBody().getStmts().get(statementPosition - 1);
    }

    private LambdaExpr getLambdaExprInStatementInMethodInClass(int statementPosition, int methodPosition, int classPosition) {
        Statement statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        VariableDeclarator variableDeclarator = (VariableDeclarator)statement.getChildrenNodes().get(0).getChildrenNodes().get(1);
        return (LambdaExpr) variableDeclarator.getInit();
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
    	Statement statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
    	ReturnStmt returnStmt = (ReturnStmt) statement;
    	ConditionalExpr conditionalExpr = (ConditionalExpr)returnStmt.getExpr();
        assertThat(conditionalExpr.getElseExpr().getClass().getName(), is(LambdaExpr.class.getName()));
    }

    @Then("the begin line is $line")
    public void thenTheBeginLineIs(int line) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(line, node.getBegin().line);
    }

    @Then("the begin column is $column")
    public void thenTheBeginColumnIs(int column) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(column, node.getBegin().column);
    }

    @Then("the end line is $line")
    public void thenTheEndLineIs(int line) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(line, node.getEnd().line);
    }

    @Then("the end column is $column")
    public void thenTheEndColumnIs(int column) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(column, node.getEnd().column);
    }

    @Then("no errors are reported")
    public void thenNoErrorsAreReported() {
        // this is present just for readability in the scenario specification
        // if the code is not parsed then exceptions are thrown before reaching this step
    }

    @Then("the package name is $package")
    public void thenThePackageNameIs(String expected) {
        PackageDeclaration node = (PackageDeclaration) state.get("selectedNode");
        assertEquals(expected, node.getPackageName());
        assertEquals(expected, node.getName().toString());
    }

    @Then("the type's diamond operator flag should be $expectedValue")
    public void thenTheUsesDiamondOperatorShouldBeBooleanAsString(boolean expectedValue) {
        ObjectCreationExpr expr = (ObjectCreationExpr) state.get("selectedNode");
        assertEquals(expectedValue, expr.getType().isUsingDiamondOperator());
    }

    @Then("the Java parser cannot parse it because of lexical errors")
    public void javaParserCannotParseBecauseOfLexicalErrors() throws ParseProblemException {
        try {
            JavaParser.parse(sourceUnderTest);
            fail("Lexical error expected");
        } catch (TokenMgrException e) {
            // ok
        }
    }

    @Then("the assignExpr produced doesn't have a null target")
    public void thenTheAssignExprProducedDoesntHaveANullTarget() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) compilationUnit.getTypes().get(0);
        ConstructorDeclaration ctor = (ConstructorDeclaration) classDeclaration.getMembers().get(1);
        ExpressionStmt assignStmt = (ExpressionStmt) ctor.getBody().getStmts().get(0);
        AssignExpr assignExpr = (AssignExpr) assignStmt.getExpression();
        assertNotNull(assignExpr.getTarget());
        assertEquals(NameExpr.class, assignExpr.getTarget().getClass());
        assertEquals(((NameExpr) assignExpr.getTarget()).getName(), "mString");
    }

    private void setSelectedNodeFromCompilationUnit(Class<? extends Node> nodeType) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        List<? extends Node> nodes = compilationUnit.getNodesByType(nodeType);
        if (nodes.size() != 1) {
            throw new RuntimeException(format("Exactly one %s expected", nodeType.getSimpleName()));
        }
        state.put("selectedNode", nodes.get(0));
    }
}
