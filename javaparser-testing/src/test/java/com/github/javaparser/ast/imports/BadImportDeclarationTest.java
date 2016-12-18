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

package com.github.javaparser.ast.imports;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ast.imports.BadImportDeclaration;
import com.github.javaparser.ast.imports.ImportDeclaration;
import org.junit.Test;

import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class BadImportDeclarationTest {
    private final JavaParser parser = new JavaParser();

    @Test
    public void whenParsingABadImportThenItIsStoredAsABadImport() {
        ParseResult<ImportDeclaration> parseResult = parser.parse(ParseStart.IMPORT_DECLARATION, provider("import static x;"));

        assertEquals("import static has only one identifier (line 1,col 16)-(line 1,col 16)", parseResult.getProblem(0).toString());
        assertEquals(true, parseResult.getResult().get() instanceof BadImportDeclaration);
    }

    @Test
    public void whenPrintingABadImportThenItIsPrintedLiterally() {
        ParseResult<ImportDeclaration> parseResult = parser.parse(ParseStart.IMPORT_DECLARATION, provider("import    static    x  ;"));

        assertEquals("???" + EOL, parseResult.getResult().get().toString());
    }

}
