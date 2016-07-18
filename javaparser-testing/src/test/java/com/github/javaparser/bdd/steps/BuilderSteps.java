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

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;

import java.util.List;
import java.util.Map;

import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;

import com.github.javaparser.ast.CompilationUnit;

public class BuilderSteps {

	/* Map that maintains shares state across step classes.  If manipulating the objects in the map you must update the state */
	private Map<String, Object> state;

	public BuilderSteps(Map<String, Object> state) {
		this.state = state;
	}

	@Given("a compilation unit with 3 imports but 2 duplicates values")
	public void givenACompilationUnitWith3ImportsBut2DuplicatesValues() {
		CompilationUnit cu = new CompilationUnit();
		state.put("cuBuilder", cu);
		cu.addImport(List.class);
		cu.addImport(Map.class);
		cu.addImport(Map.class);
	}

	@Then("the compilation unit has 2 imports")
	public void thenTheCompilationUnitHas2Imports() {
		CompilationUnit cu = (CompilationUnit) state.get("cuBuilder");
		assertThat(cu.getImports().size(), is(2));
	}

}
