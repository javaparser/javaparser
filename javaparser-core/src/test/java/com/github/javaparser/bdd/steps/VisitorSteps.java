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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericListVisitorAdapter;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.bdd.visitors.PositionTestVisitor;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;

public class VisitorSteps {

    /* Fields used to maintain step state within this step class */
    private VoidVisitorAdapter<AtomicReference<String>> toUpperCaseVariableNameVisitor;
    private VoidVisitorAdapter<AtomicReference<String>> collectVariableNameVisitor;
    private PositionTestVisitor positionTestVisitor;
    private GenericVisitorAdapter<String, Void> nameReturningVisitor;
    private GenericListVisitorAdapter<String, Void> allNameReturningVisitor;
    private AtomicReference<String> collectedVariableName;
    private String returnedVariableName;
    private List<String> returnedVariableNames;

    /* Map that maintains shares state across step classes.  If manipulating the objects in the map you must update the state */
    private Map<String, Object> state;

    public VisitorSteps(Map<String, Object> state) {
        this.state = state;
    }

    @Given("a VoidVisitorAdapter with a visit method that changes variable names to uppercase")
    public void givenAVoidVisitorAdapterWithAVisitMethodThatChangesVariableNamesToUppercase() {
        toUpperCaseVariableNameVisitor = new VoidVisitorAdapter<AtomicReference<String>>() {
            @Override
            public void visit(VariableDeclarator n, AtomicReference<String> arg) {
                n.setName(n.getNameAsString().toUpperCase());
            }
        };
    }

    @Given("a VoidVisitorAdapter with a visit method and collects the variable names")
    public void givenAVoidVisitorAdapterWithAVisitMethodThatCollectsTheVariableName() {
        collectVariableNameVisitor = new VoidVisitorAdapter<AtomicReference<String>>() {
            @Override
            public void visit(VariableDeclarator n, AtomicReference<String> arg) {
                arg.set(arg.get() + n.getName() + ";");
            }

            @Override
            public void visit(Parameter n, AtomicReference<String> arg) {
                arg.set(arg.get() + n.getName() + ";");
            }
        };
    }

    @Given("a GenericVisitorAdapter with a visit method that returns variable names")
    public void givenAGenericVisitorAdapterWithAVisitMethodThatReturnsVariableNames() {
        nameReturningVisitor = new GenericVisitorAdapter<String, Void>() {
            @Override
            public String visit(VariableDeclarator n, Void arg) {
                return n.getNameAsString();
            }
        };
    }

    @Given("a GenericListVisitorAdapter with a visit method that returns all variable names")
    public void givenAGenericListVisitorAdapterWithAVisitMethodThatReturnsAllVariableNames() {
        allNameReturningVisitor = new GenericListVisitorAdapter<String, Void>() {
            @Override
            public List<String> visit(VariableDeclarator n, Void arg) {
                return Collections.singletonList(n.getNameAsString());
            }
        };
    }

    @Given("a VoidVisitorAdapter with a visit method that asserts sensible line positions")
    public void givenAVoidVisitorAdapterWithAVisitMethodThatAssertsSensibleLinePositions() {
        positionTestVisitor = new PositionTestVisitor();
    }

    @When("the CompilationUnit is cloned to the second CompilationUnit")
    public void whenTheSecondCompilationUnitIsCloned() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        CompilationUnit compilationUnit2 = (CompilationUnit) compilationUnit.accept(new CloneVisitor(), null);
        state.put("cu2", compilationUnit2);
    }

    @When("the CompilationUnit is visited by the to uppercase visitor")
    public void whenTheCompilationUnitIsVisitedByTheVistor() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        toUpperCaseVariableNameVisitor.visit(compilationUnit, null);
        state.put("cu1", compilationUnit);
    }

    @When("the CompilationUnit is visited by the variable name collector visitor")
    public void whenTheCompilationUnitIsVisitedByTheVariableNameCollectorVisitor() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        collectedVariableName = new AtomicReference<>("");
        collectVariableNameVisitor.visit(compilationUnit, collectedVariableName);
    }

    @When("the CompilationUnit is visited by the visitor that returns variable names")
    public void whenTheCompilationUnitIsVisitedByTheVisitorThatReturnsVariableNames() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        returnedVariableName = nameReturningVisitor.visit(compilationUnit, null);
    }

    @When("the CompilationUnit is visited by the visitor that returns all variable names")
    public void whenTheCompilationUnitIsVisitedByTheVisitorThatReturnsAllVariableNames() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        returnedVariableNames = allNameReturningVisitor.visit(compilationUnit, null);
    }

    @When("the CompilationUnit is visited by the PositionTestVisitor")
    public void whenTheCompilationUnitIsVisitedByThePositionTestVisitor() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        compilationUnit.accept(positionTestVisitor, null);
    }

    @Then("the collected variable name is \"$nameUnderTest\"")
    public void thenTheCollectedVariableNameIs(String nameUnderTest) {
        assertThat(collectedVariableName.get(), is(nameUnderTest));
    }

    @Then("the return variable name is \"$nameUnderTest\"")
    public void thenTheReturnVariableNameIs(String nameUnderTest) {
        assertThat(returnedVariableName, is(nameUnderTest));
    }

    @Then("the first return variable name is \"$nameUnderTest\"")
    public void thenTheFirstReturnVariableNameIs(String nameUnderTest) {
        assertThat(returnedVariableNames.get(0), is(nameUnderTest));
    }

    @Then("the total number of nodes visited is $expectedCount")
    public void thenTheTotalNumberOfNodesVisitedIs(int expectedCount) {
        assertThat(positionTestVisitor.getNumberOfNodesVisited(), is(expectedCount));
    }
}
