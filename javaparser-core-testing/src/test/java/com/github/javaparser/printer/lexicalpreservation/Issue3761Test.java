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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.FieldDeclaration;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.stream.Collectors;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue3761Test extends AbstractLexicalPreservingTest {

    @Test
    public void test() {
    	considerCode(
        		"class C { \n"
        		+ "    static String S = \"s\";\n"
        		+ "}");

        FieldDeclaration field = cu.findAll(FieldDeclaration.class).get(0);

		List<Modifier.Keyword> kws = field.getModifiers().stream().map(Modifier::getKeyword).collect(Collectors.toList());
		kws.add(0, Modifier.Keyword.PROTECTED);
		field.setModifiers(kws.toArray(new Modifier.Keyword[] {}));
        
        String expected = 
        		"class C { \r\n"
        		+ "    protected static String S = \"s\";\r\n"
        		+ "}";

        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

}
