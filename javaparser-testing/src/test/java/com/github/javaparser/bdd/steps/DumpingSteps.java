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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.Node;

import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.StringReader;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.assertThat;

public class DumpingSteps {

    private Node resultNode;
    private String sourceUnderTest;

    @Given("the {class|compilation unit|expression|block|expressions|statement|import|annotation|body declaration}:$classSrc")
    public void givenTheClass(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @When("the {class|compilation unit} is parsed by the Java parser")
    public void whenTheClassIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parse(new StringReader(sourceUnderTest), true);
    }

    @When("the expression is parsed by the Java parser")
    public void whenTheExpressionIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parseExpression(sourceUnderTest);
    }

    @When("the block is parsed by the Java parser")
    public void whenTheBlockIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parseBlock(sourceUnderTest);
    }

    @When("the statement is parsed by the Java parser")
    public void whenTheStatementIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parseStatement(sourceUnderTest);
    }

    @When("the import is parsed by the Java parser")
    public void whenTheImportIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parseImport(sourceUnderTest);
    }

    @When("the annotation is parsed by the Java parser")
    public void whenTheAnnotationIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parseAnnotation(sourceUnderTest);
    }

    @When("the body declaration is parsed by the Java parser")
    public void whenTheBodyDeclarationIsParsedByTheJavaParser() throws ParseException {
        resultNode = JavaParser.parseBodyDeclaration(sourceUnderTest);
    }

    @Then("it is dumped to:$dumpSrc")
    public void isDumpedTo(String dumpSrc) {
        assertThat(resultNode.toString().trim(), is(dumpSrc.trim()));
    }

}
