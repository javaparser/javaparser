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

package com.github.javaparser.steps;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.utils.Utils.readerToString;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class PrettyPrintingSteps {

    private Node resultNode;
    private String sourceUnderTest;

    @Given("the {class|compilation unit|expression|block|statement|import|annotation|body|class body|interface body}:$classSrc")
    public void givenTheClass(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @Given("the {class|compilation unit|expression|block|statement|import|annotation|body|class body|interface body} in the file \"$classFile\"")
    public void givenTheClassInTheFile(String classFile) throws URISyntaxException, IOException {
        URL url = getClass().getResource("../samples/" + classFile);
        sourceUnderTest = readerToString(new FileReader(new File(url.toURI()))).trim();
    }

    @When("the {class|compilation unit} is parsed by the Java parser")
    public void whenTheClassIsParsedByTheJavaParser() {
        resultNode = parse(sourceUnderTest);
    }

    @When("the expression is parsed by the Java parser")
    public void whenTheExpressionIsParsedByTheJavaParser() {
        resultNode = parseExpression(sourceUnderTest);
    }

    @When("the block is parsed by the Java parser")
    public void whenTheBlockIsParsedByTheJavaParser() {
        resultNode = parseBlock(sourceUnderTest);
    }

    @When("the statement is parsed by the Java parser")
    public void whenTheStatementIsParsedByTheJavaParser() {
        resultNode = parseStatement(sourceUnderTest);
    }

    @When("the import is parsed by the Java parser")
    public void whenTheImportIsParsedByTheJavaParser() {
        resultNode = parseImport(sourceUnderTest);
    }

    @When("the annotation is parsed by the Java parser")
    public void whenTheAnnotationIsParsedByTheJavaParser() {
        resultNode = parseAnnotation(sourceUnderTest);
    }

    @When("the annotation body declaration is parsed by the Java parser")
    public void whenTheBodyDeclarationIsParsedByTheJavaParser() {
        resultNode = parseAnnotationBodyDeclaration(sourceUnderTest);
    }

    @When("the class body declaration is parsed by the Java parser")
    public void whenTheClassBodyDeclarationIsParsedByTheJavaParser() {
        resultNode = parseBodyDeclaration(sourceUnderTest);
    }

    @When("the interface body declaration is parsed by the Java parser")
    public void whenTheInterfaceBodyDeclarationIsParsedByTheJavaParser() {
        resultNode = parseBodyDeclaration(sourceUnderTest);
    }

    @When("the class is visited by an empty ModifierVisitorAdapter")
    public void whenTheClassIsVisitedByAnEmptyModifierVisitorAdapter() {
        (new ModifierVisitor<Void>() {
        }).visit((CompilationUnit) resultNode, null);
    }

    @Then("it is printed as:$src")
    public void isPrintedAs(String src) {
        assertEquals(src.trim(), resultNode.toString().trim());
    }
}
