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

import com.github.javaparser.*;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import static org.junit.Assert.*;

public class PositionRangeSteps {

	private Position position;
	private Position secondPosition;

    /*
	 * Given steps
     */

	@Given("the position $x, $y")
	public void givenThePosition(int x, int y) {
		this.position = new Position(x, y);
	}


    /*
     * When steps
     */

	@When("I compare to position $x, $y")
	public void iCompareToPosition(int x, int y) {
		secondPosition = new Position(x, y);
	}

    /*
     * Then steps
     */

	@Then("the positions are equal")
	public void thenThePositionsAreEqual() {
		assertEquals(position, secondPosition);
	}

	@Then("it is after the first position")
	public void thenItIsAfterTheFirstPosition() {
		assertTrue(secondPosition.isAfter(position));
	}

	@Then("it is before the first position")
	public void thenItIsBeforeTheFirstPosition() {
		assertTrue(secondPosition.isBefore(position));
	}

	@Then("the positions are not equal")
	public void thenThePositionsAreNotEqual() {
		assertFalse(position.equals(secondPosition));
	}

	@Then("it is not after the first position")
	public void thenItIsNotAfterTheFirstPosition() {
		assertFalse(secondPosition.isAfter(position));
	}

	@Then("it is not before the first position")
	public void thenItIsNotBeforeTheFirstPosition() {
		assertFalse(secondPosition.isBefore(position));
	}
}
