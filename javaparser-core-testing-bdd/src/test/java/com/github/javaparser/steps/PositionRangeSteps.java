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

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import org.jbehave.core.annotations.BeforeScenario;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import static com.github.javaparser.Position.pos;
import static com.github.javaparser.Range.range;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

public class PositionRangeSteps {

    private Position position;
    private Position secondPosition;
    private Range range;
    private Range secondRange;

    @BeforeScenario
    public void reset() {
        position = null;
        secondPosition = null;
        range = null;
        secondRange = null;
    }
    /*
	 * Given steps
     */

    @Given("the position $line, $column")
    public void givenThePosition(int line, int column) {
        this.position = pos(line, column);
    }

    @Given("the range $line1, $column1 - $line2, $column2")
    public void givenTheRange(int line1, int column1, int line2, int column2) {
        this.range = range(line1, column1, line2, column2);
    }

    /*
	 * When steps
     */

    @When("I compare to position $line, $column")
    public void iCompareToPosition(int line, int column) {
        secondPosition = pos(line, column);
    }

    @When("I compare to range $line1, $column1 - $line2, $column2")
    public void whenICompareToRange(int line1, int column1, int line2, int column2) {
        this.secondRange = range(line1, column1, line2, column2);
    }

    /*
	 * Then steps
     */

    @Then("the positions are equal")
    public void thenThePositionsAreEqual() {
        assertThat(position.equals(secondPosition), is(true));
    }

    @Then("it is after the {first|} position")
    public void thenItIsAfterTheFirstPosition() {
        if (secondPosition != null) {
            assertThat(secondPosition.isAfter(position), is(true));
        } else {
            assertThat(secondRange.isAfter(position), is(true));
        }
    }

    @Then("it is before the {first|} position")
    public void thenItIsBeforeTheFirstPosition() {
        if (secondPosition != null) {
            assertThat(secondPosition.isBefore(position), is(true));
        } else {
            assertThat(secondRange.isBefore(position), is(true));
        }
    }

    @Then("the positions are not equal")
    public void thenThePositionsAreNotEqual() {
        assertThat(position.equals(secondPosition), is(false));
    }

    @Then("it is not after the {first|} position")
    public void thenItIsNotAfterTheFirstPosition() {
        assertThat(secondPosition.isAfter(position), is(false));
    }

    @Then("it is not before the {first|} position")
    public void thenItIsNotBeforeTheFirstPosition() {
        assertThat(secondPosition.isBefore(position), is(false));
    }

    @Then("the ranges are equal")
    public void theRangesAreEqual() {
        assertThat(range.equals(secondRange), is(true));
    }

    @Then("it is contained in the first range")
    public void itIsContainedInTheFirstRange() {
        assertThat(range.contains(secondRange), is(true));
    }
}
