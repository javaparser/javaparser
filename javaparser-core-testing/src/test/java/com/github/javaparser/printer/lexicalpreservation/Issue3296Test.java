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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue3296Test extends AbstractLexicalPreservingTest  {
    
    @Test
    public void test() {
        considerCode("public class Test { String[][] allTest; }");
        String expected = "public class Test { @Nullable\n" + 
                "String[][] allTest; }";
        Optional<ClassOrInterfaceDeclaration> clazzOptional = cu.getClassByName("Test");
        assertTrue(clazzOptional.isPresent());
        ClassOrInterfaceDeclaration clazz = clazzOptional.get();
        clazz.getMembers().forEach(
                bodyDeclaration ->
                        bodyDeclaration.ifFieldDeclaration(
                                fieldDeclaration -> {
                                    NodeList<VariableDeclarator> vars =
                                            fieldDeclaration.asFieldDeclaration().getVariables();
                                    for (VariableDeclarator v : vars) {
                                        if (v.getName().toString().equals("allTest")) {
                                            fieldDeclaration.addMarkerAnnotation("Nullable");
                                            break;
                                        }
                                    }
                                }));
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }
}
