/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.generator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.SourceRoot;

import java.util.List;

public abstract class CompilationUnitGenerator extends Generator {

	protected CompilationUnitGenerator(SourceRoot sourceRoot) {
		super(sourceRoot);
	}

	@Override
	public void generate() throws Exception {
		List<ParseResult<CompilationUnit>> parsedCus = sourceRoot.tryToParse();
		for (ParseResult<CompilationUnit> cu : parsedCus) {
			cu.ifSuccessful(this::generateCompilationUnit);
		}
	}

	protected abstract void generateCompilationUnit(CompilationUnit compilationUnit);

}
