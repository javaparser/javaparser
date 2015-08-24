/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import com.github.javaparser.ASTHelper;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.util.List;
import java.util.Map;

import static com.github.javaparser.bdd.steps.SharedSteps.getMemberByTypeAndPosition;
import static com.github.javaparser.bdd.steps.SharedSteps.getMethodByPositionAndClassPosition;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsNull.notNullValue;
import static org.hamcrest.core.IsNull.nullValue;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;

public class ParsingSteps {

    private Map<String, Object> state;

    public ParsingSteps(Map<String, Object> state){
        this.state = state;
    }

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

        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
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
        Statement statement = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        LambdaExpr lambdaExpr = (LambdaExpr) statement.getChildrenNodes().get(0).getChildrenNodes().get(1).getChildrenNodes().get(1)
                .getChildrenNodes().get(1).getChildrenNodes().get(2);
        assertThat(lambdaExpr.getBody().toString(), is(expectedBody));
    }

    @Then("lambda in statement $statementPosition in method $methodPosition in class $classPosition block statement is null")
    public void thenLambdaInStatementInMethodInClassBlockStatementIsNull(int statementPosition, int methodPosition, int classPosition) {
        LambdaExpr lambdaExpr = getLambdaExprInStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        BlockStmt blockStmt = (BlockStmt) lambdaExpr.getBody();
        assertThat(blockStmt.getStmts(), is(nullValue()));
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
        Statement statementUnderTest = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        MethodReferenceExpr methodReferenceUnderTest =
                (MethodReferenceExpr) statementUnderTest.getChildrenNodes().get(0).getChildrenNodes().get(2);
        assertThat(methodReferenceUnderTest.getScope().toString(), is(expectedName));
    }

    @Then("method reference in statement $statementPosition in method $methodPosition in class $classPosition identifier is $expectedName")
    public void thenMethodReferenceInStatementInMethodInClassIdentifierIsCompareByAge(int statementPosition, int methodPosition,
                                                                                      int classPosition, String expectedName) {
        Statement statementUnderTest = getStatementInMethodInClass(statementPosition, methodPosition, classPosition);
        MethodReferenceExpr methodReferenceUnderTest =
                (MethodReferenceExpr) statementUnderTest.getChildrenNodes().get(0).getChildrenNodes().get(2);
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
        assertEquals(line, node.getBeginLine());
    }

    @Then("the begin column is $column")
    public void thenTheBeginColumnIs(int column) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(column, node.getBeginColumn());
    }

    @Then("the end line is $line")
    public void thenTheEndLineIs(int line) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(line, node.getEndLine());
    }

    @Then("the end column is $column")
    public void thenTheEndColumnIs(int column) {
        Node node = (Node) state.get("selectedNode");
        assertEquals(column, node.getEndColumn());
    }

    @When("I take the ArrayCreationExpr")
    public void iTakeTheArrayCreationExpr() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        List<ArrayCreationExpr> arrayCreationExprs = ASTHelper.getNodesByType(compilationUnit, ArrayCreationExpr.class);
        if (arrayCreationExprs.size() != 1) {
            throw new RuntimeException("Exactly one ArrayCreationExpr expected");
        }
        state.put("selectedNode", arrayCreationExprs.get(0));
    }
}
