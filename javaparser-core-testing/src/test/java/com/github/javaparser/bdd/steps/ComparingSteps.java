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
import com.github.javaparser.ast.CompilationUnit;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class ComparingSteps {

    private CompilationUnit first;
    private CompilationUnit second;

    /*
     * Given steps
     */

    @Given("the first class:$classSrc")
    public void givenTheFirstClass(String classSrc) {
        this.first = JavaParser.parse(classSrc.trim());
    }

    @Given("the second class:$classSrc")
    public void givenTheSecondClass(String classSrc) {
        this.second = JavaParser.parse(classSrc.trim());
    }

    /*
     * Then steps
     */

    @Then("they are equals")
    public void thenTheyAreEquals() {
        assertThat(first, is(equalTo(second)));
    }

}
