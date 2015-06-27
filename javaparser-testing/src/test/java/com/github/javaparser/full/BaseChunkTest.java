/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.full;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.Node;
import com.github.javaparser.full.utils.BulkTestClass;
import com.github.javaparser.full.utils.BulkTestRunner;
import com.github.javaparser.full.utils.NormalizedJsonWriter;
import com.github.javaparser.full.utils.TestResources;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;

/**
 * @author Didier Villevalois
 */
@RunWith(BulkTestRunner.class)
public abstract class BaseChunkTest<N extends Node> implements BulkTestClass {

    @Rule
    public ExpectedException exception = ExpectedException.none();

    protected abstract N parse(String content) throws ParseException;

    @Override
    public void runTest(TestResources resources) throws Exception {
        String source = resources.getResourceAsString("source.txt");
        String normalized = resources.getResourceAsString("normalized.txt");
        String failure = resources.getResourceAsString("failure.txt");

        if (normalized != null) {
            N expression = parse(source);
            String actual = NormalizedJsonWriter.write(expression);
            Assert.assertEquals(normalized, actual);
        } else if (failure != null) {
            exception.expect(ParseException.class);
            exception.expectMessage(failure);
            parse(source);
        } else {
            throw new IllegalStateException("There should be either a normalized.txt or a failure.txt file");
        }
    }
}
