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

package com.github.javaparser.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseClassOrInterfaceType;
import static org.junit.Assert.assertEquals;

public class NodeWithThrownExceptionsBuildersTest {
    private final CompilationUnit cu = new CompilationUnit();

    @Test
    public void testThrows() {
        MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
        addMethod.addThrownException(IllegalStateException.class);
        assertEquals(1, addMethod.getThrownExceptions().size());
        assertEquals(true, addMethod.isThrown(IllegalStateException.class));
        addMethod.addThrownException(parseClassOrInterfaceType("Test"));
        assertEquals(2, addMethod.getThrownExceptions().size());
        assertEquals("Test", addMethod.getThrownException(1).toString());
    }
}
