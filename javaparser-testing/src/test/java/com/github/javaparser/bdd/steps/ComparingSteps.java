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
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.StringReader;
import java.util.List;
import java.util.Map;

import static com.github.javaparser.bdd.steps.SharedSteps.getMemberByTypeAndPosition;
import static com.github.javaparser.bdd.steps.SharedSteps.getMethodByPositionAndClassPosition;
import static org.hamcrest.Matchers.empty;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsNull.notNullValue;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;

public class ComparingSteps {

    private Map<String, Object> state;
    private CompilationUnit first;
    private CompilationUnit second;
    private boolean equalsResult;

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
        assertEquals("they are equals", first, second);
    }

}
