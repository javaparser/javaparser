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

import static com.github.javaparser.ast.NodeList.*;
import static com.github.javaparser.ast.type.PrimitiveType.*;
import static com.github.javaparser.bdd.steps.SharedSteps.getMethodByPositionAndClassPosition;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertThat;

import java.util.EnumSet;
import java.util.Map;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.jbehave.core.annotations.Alias;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class ManipulationSteps {

    /* Fields used to maintain step state within this step class */
    private BlockStmt blockStmt;
    private Statement statement;
    private TryStmt tryStmt;
    private NodeList<VariableDeclarationExpr> variableDeclarationExprList;
    private ChangeMethodNameToUpperCaseVisitor changeMethodNameToUpperCaseVisitor;
    private AddNewIntParameterCalledValueVisitor addNewIntParameterCalledValueVisitor;

    /* Map that maintains shares state across step classes.  If manipulating the objects in the map you must update the state */
    private Map<String, Object> state;

    public ManipulationSteps(Map<String, Object> state){
        this.state = state;
    }

    @Given("a BlockStmt")
    public void givenABlockStatement() {
        blockStmt = new BlockStmt();
    }

    @Given("a Statement")
    public void givenAStatement() {
        statement = null;
    }

    @Given("a TryStmt")
    public void givenATryStmt() {
        tryStmt = new TryStmt();
    }

    @Given("a List of VariableDeclarations")
    public void givenAListOfVariableDeclarations() {
        variableDeclarationExprList = new NodeList<>();
        variableDeclarationExprList.add(new VariableDeclarationExpr());
        variableDeclarationExprList.add(new VariableDeclarationExpr());
    }

    @Given("a ChangeNameToUpperCaseVisitor")
    public void givenAChangeNameToUpperCaseVisitor() {
        changeMethodNameToUpperCaseVisitor = new ChangeMethodNameToUpperCaseVisitor();
    }

    @Given("a AddNewIntParameterCalledValueVisitor")
    public void givenAAddNewParameterCalledValueVisitor() {
        addNewIntParameterCalledValueVisitor = new AddNewIntParameterCalledValueVisitor();
    }

    @When("is the String \"$value\" is parsed by the JavaParser using parseBlock")
    public void whenIsTheStringIsParsedByTheJavaParser(String value) {
        blockStmt = JavaParser.parseBlock(value);
    }

    @When("is the String \"$value\" is parsed by the JavaParser using parseStatement")
    public void whenIsTheStringIsParsedByTheJavaParserUsingParseStatement(String value) {
        statement= JavaParser.parseStatement(value);
    }

    @When("the List of VariableDeclarations are set as the resources on TryStmt")
    public void whenTheListOfVariableDeclarationsAreSetAsTheResourcesOnTryStmt() {
        tryStmt.setResources(variableDeclarationExprList);
    }

    @When("empty list is set as the resources on TryStmt")
    public void whenNullIsSetAsTheResourcesOnTryStmt() {
        tryStmt.setResources(new NodeList<>());
    }

    @When("the package declaration is set to \"$packageName\"")
    public void whenThePackageDeclarationIsSetTo(String packageName) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        compilationUnit.setPackage(new PackageDeclaration(new NameExpr(packageName)));
        state.put("cu1", compilationUnit);
    }

    @When("a public class called \"$className\" is added to the CompilationUnit")
    public void whenAClassCalledIsAddedToTheCompilationUnit(String className) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
		TypeDeclaration<?> type = new ClassOrInterfaceDeclaration(EnumSet.of(Modifier.PUBLIC), false, "CreateClass");
        compilationUnit.setTypes(nodeList(type));
        state.put("cu1", compilationUnit);
    }

    @When("a public static method called \"$methodName\" returning void is added to class $position in the compilation unit")
    public void whenAStaticMethodCalledReturningIsAddedToClassInTheCompilationUnit(String methodName, int position) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
		 TypeDeclaration<?> type = compilationUnit.getTypes().get(position -1);
		EnumSet<Modifier> modifiers = EnumSet.of(Modifier.PUBLIC);
		MethodDeclaration method = new MethodDeclaration(modifiers, new VoidType(), methodName);
		modifiers.add(Modifier.STATIC);
		method.setModifiers(modifiers);
        type.addMember(method);
        state.put("cu1", compilationUnit);
    }

    @When("$typeName varargs called \"$parameterName\" are added to method $methodPosition in class $classPosition")
    public void whenVarargsCalledAreAddedToMethodInClass(String typeName, String parameterName, int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        Parameter param = Parameter.create(new ClassOrInterfaceType(typeName), parameterName);
        param.setVarArgs(true);
        method.addParameter(param);
    }

    @When("a BlockStmt is added to method $methodPosition in class $classPosition")
    public void whenABlockStmtIsAddedToMethodInClass(int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        method.setBody(new BlockStmt());
    }

    @When("$className.$fieldName.$methodName(\"$stringValue\"); is added to the body of method $methodPosition in class $classPosition")
    public void whenHelloWorldIsAddedToTheBodyOfMethodInClass(String className, String fieldName, String methodName, String stringValue,
                                                              int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        NameExpr clazz = new NameExpr(className);
        FieldAccessExpr field = new FieldAccessExpr(clazz, fieldName);
        MethodCallExpr call = new MethodCallExpr(field, methodName);
        call.addArgument(new StringLiteralExpr(stringValue));
        method.getBody().addStatement(call);
    }

    @When("method $methodPosition in class $classPosition has it's name converted to uppercase")
    public void whenMethodInClassHasItsNameConvertedToUppercase(int methodPosition, int classPosition) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        method.setName(method.getName().toUpperCase());
    }

    @When("method $methodPosition in class $classPosition has an int parameter called \"$paramName\" added")
    public void whenMethodInClassHasAnIntArgumentCalledAdded(int methodPosition, int classPosition, String paramName) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        method.addParameter(INT_TYPE, paramName);
    }

    @When("the compilation unit is cloned")
    public void whenTheCompilationUnitIsCloned() throws CloneNotSupportedException {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        state.put("cu1", compilationUnit.clone());
    }

    @When("the ChangeNameToUpperCaseVisitor visits to compilation unit")
    public void whenTheVisitorVisitsToCompilationUnit() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        changeMethodNameToUpperCaseVisitor.visit(compilationUnit, null);
        state.put("cu1", compilationUnit);
    }

    @When("the AddNewIntParameterCalledValueVisitor visits to compilation unit")
    public void whenTheAddNewParameterCalledValueVisitorVisitsToCompilationUnit() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        addNewIntParameterCalledValueVisitor.visit(compilationUnit, null);
        state.put("cu1", compilationUnit);
    }

    @Then("is not equal to null")
    public void thenIsNotEqualToNull() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        assertNotEquals(compilationUnit, null);
    }

    @Then("is not equal to $value")
    public void thenIsNotEqualTo(String value) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        assertNotEquals(compilationUnit, value);
    }

    @Then("Statement $position in BlockStmt toString is \"$expectedContent\"")
    public void thenTheBlockStmtContentIs(int position, String expectedContent) {
        Statement statementUnderTest = blockStmt.getStmts().get(position-1);
        assertThat(statementUnderTest.toString(), is(expectedContent));
    }

    @Then("Statement toString is \"$expectedContent\"")
    public void thenStatementToStringIsxXy(String expectedContent) {
        assertThat(statement.toString(), is(expectedContent));
    }

    @Then("all the VariableDeclarations parent is the TryStmt")
    public void thenAllTheVariableDeclarationsParentIsTheTryStmt() {
        for(VariableDeclarationExpr expr : variableDeclarationExprList){
            assertThat(expr.getParentNode().getParentNode(), is((Node)tryStmt));
        }
    }

    @Then("the TryStmt has no child nodes")
    public void thenTheTryStmtHasNotChildNodes() {
        assertThat(tryStmt.getChildrenNodes().size(), is(0));
    }

    @Then("method $methodPosition in class $classPosition has the name \"$expectedName\"")
    public void thenMethodInClassHasTheName(int methodPosition, int classPosition, String expectedName) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        assertThat(method.getName(), is(expectedName));
    }

    @Then("method $methodPosition in class $classPosition has $expectedCount parameters")
    @Alias("method $methodPosition in class $classPosition has $expectedCount parameter")
    public void thenMethodInClassHasArguments(int methodPosition, int classPosition, int expectedCount) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);

        assertThat(method.getParameters().size(), is(expectedCount));
    }

    @Then("method $methodPosition in class $classPosition parameter $parameterPosition is type int called \"$expectedName\"")
    public void thenMethodInClassParameterIsTypeIntCalled(int methodPosition, int classPosition, int parameterPosition, String expectedName) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        MethodDeclaration method = getMethodByPositionAndClassPosition(compilationUnit, methodPosition, classPosition);
        Parameter parameter = method.getParameters().get(parameterPosition -1);
        assertThat(parameter.getType(), is(INT_TYPE));
        assertThat(parameter.getId().getName(), is(expectedName));
    }

    private static class ChangeMethodNameToUpperCaseVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            n.setName(n.getName().toUpperCase());
        }
    }

    private static class AddNewIntParameterCalledValueVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            n.addParameter(INT_TYPE, "value");
        }
    }
}

