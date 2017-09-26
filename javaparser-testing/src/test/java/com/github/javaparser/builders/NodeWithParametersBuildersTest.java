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
import com.github.javaparser.ast.body.Parameter;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.List;

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class NodeWithParametersBuildersTest {
    private final CompilationUnit cu = new CompilationUnit();

    @Test
    public void testAddParameter() {
        MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
        addMethod.addParameter(int.class, "yay");
        Parameter myNewParam = addMethod.addAndGetParameter(List.class, "myList");
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + List.class.getName() + ";" + EOL, cu.getImport(0).toString());
        assertEquals(2, addMethod.getParameters().size());
        assertEquals("yay", addMethod.getParameter(0).getNameAsString());
        assertEquals("List", addMethod.getParameter(1).getType().toString());
        assertEquals(myNewParam, addMethod.getParameter(1));
    }

    @Test
    public void testGetParamByName() {
        MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
        Parameter addAndGetParameter = addMethod.addAndGetParameter(int.class, "yay");
        assertEquals(addAndGetParameter, addMethod.getParameterByName("yay").get());
    }

    @Test
    public void testGetParamByType() {
        MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
        Parameter addAndGetParameter = addMethod.addAndGetParameter(int.class, "yay");
        assertEquals(addAndGetParameter, addMethod.getParameterByType("int").get());
        assertEquals(addAndGetParameter, addMethod.getParameterByType(int.class).get());
    }

}
