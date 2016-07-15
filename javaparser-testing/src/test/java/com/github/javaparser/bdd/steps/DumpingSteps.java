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
import com.github.javaparser.SourcesHelper;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.DumpVisitor;

import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import java.net.URISyntaxException;
import java.net.URL;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;

public class DumpingSteps {

    private CompilationUnit compilationUnit;
    private String sourceUnderTest;

    @Given("the class:$classSrc")
    public void givenTheClass(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @Given("the class in the file \"$classFile\"")
    public void givenTheClassInTheFile(String classFile) throws URISyntaxException, IOException, ParseException {
        URL url = getClass().getResource("../samples/" + classFile);
        sourceUnderTest = SourcesHelper.readerToString(new FileReader(new File(url.toURI()))).trim();
    }

    @Given("the compilation unit:$classSrc")
    public void givenTheCompilationUnit(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @When("the class is parsed by the Java parser")
    public void whenTheClassIsParsedByTheJavaParser() throws ParseException {
        compilationUnit = JavaParser.parse(new StringReader(sourceUnderTest), true);
    }

    @Then("it is dumped to:$dumpSrc")
    public void isDumpedTo(String dumpSrc) {
        DumpVisitor dumpVisitor = new DumpVisitor();
        dumpVisitor.visit(compilationUnit, null);
        assertEquals(dumpSrc.trim(), dumpVisitor.getSource().trim());
    }

}
