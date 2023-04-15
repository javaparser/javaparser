/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.SimpleName;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertTrue;


public class Issue2592Test extends AbstractLexicalPreservingTest {

    @Test
    public void testLPP() {

        considerCode("public class A {" +
                "  public void m(final int a_original, int b) {" +
                "  }" +
                "} ");
        Optional<MethodDeclaration> md = cu.findFirst(MethodDeclaration.class);
        //all parameters have parent nodes here
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));

        //all parameters have parent nodes here
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));


        //add a third parameter
        md.get().addParameter("String", "c_brand_new");

        //seems like we can add a parameter fine (and all of the parents still assigned)
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));


//        md.get().getParameters().forEach(p -> System.out.println(p + " parent " + p.getParentNode().isPresent()));
        Parameter p1 = md.get().getParameter(0);
        Parameter p2 = new Parameter(p1.getModifiers(), p1.getType(), new SimpleName("a_renamed"));

        //here we replace a parameter
        boolean isReplaced = md.get().replace(p1, p2);
        assertTrue(isReplaced); //the replacement seemed to work


        //...however when we replaced the parent nodes (for the replaced node AND the added node (after the replaced node) now null
//        md.get().getParameters().forEach(p -> System.out.println(p + " parent " + p.getParentNode().isPresent()));
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));
    }

}
