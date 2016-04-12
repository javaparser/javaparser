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
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.*;
import com.github.javaparser.ast.visitor.DumpVisitor;

import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.ByteArrayInputStream;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.assertThat;

public class DumpingSteps {

    private CompilationUnit compilationUnit;
    private CommentsCollection commentsCollection;
    private String sourceUnderTest;

    @Given("the class:$classSrc")
    public void givenTheClass(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @Given("the compilation unit:$classSrc")
    public void givenTheCompilationUnit(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @When("the class is parsed by the Java parser")
    public void whenTheClassIsParsedByTheJavaParser() throws ParseException {
        compilationUnit = JavaParser.parse(new ByteArrayInputStream(sourceUnderTest.getBytes()));
    }

    @Then("it is dumped to:$dumpSrc")
    public void isDumpedTo(String dumpSrc) {
        DumpVisitor dumpVisitor = new DumpVisitor();
        dumpVisitor.visit(compilationUnit, null);
        assertThat(dumpVisitor.getSource().trim(), is(dumpSrc.trim()));
    }

}
