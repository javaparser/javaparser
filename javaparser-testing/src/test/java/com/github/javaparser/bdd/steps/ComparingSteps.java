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
import static org.hamcrest.CoreMatchers.*;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;

import java.io.StringReader;
import java.util.Map;

import static org.junit.Assert.*;

public class ComparingSteps {

    private Map<String, Object> state;
    private CompilationUnit first;
    private CompilationUnit second;

    public ComparingSteps(Map<String, Object> state){
        this.state = state;
    }

    /*
     * Given steps
     */

    @Given("the first class:$classSrc")
    public void givenTheFirstClass(String classSrc) throws ParseException {
        this.first = JavaParser.parse(new StringReader(classSrc.trim()), true);
    }

    @Given("the second class:$classSrc")
    public void givenTheSecondClass(String classSrc) throws ParseException {
        this.second = JavaParser.parse(new StringReader(classSrc.trim()), true);
    }

    /*
     * Then steps
     */

    @Then("they are equals")
    public void thenTheyAreEquals() {
        assertThat(first, is(equalTo(second)));
    }

}
