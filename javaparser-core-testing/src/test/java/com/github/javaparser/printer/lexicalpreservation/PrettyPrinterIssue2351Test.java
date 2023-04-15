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

import com.github.javaparser.ast.body.EnumDeclaration;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertTrue;

// manage java.lang.UnsupportedOperationException: Csm token token(}) NodeText TOKEN ";"   <102>   (line 1,col 39)-(line 1,col 39)
class PrettyPrinterIssue2351Test extends AbstractLexicalPreservingTest  {

    @Test
    void printingEnum2() {
        String def2 = 
                "public enum RandomEnum {" + 
                " TYPE_1;" +
                "}";
        considerCode(def2);
        Optional<EnumDeclaration> decl = cu.findFirst(EnumDeclaration.class);
        if (decl.isPresent()) decl.get().addEnumConstant("SOMETHING");
        assertTrue(decl.get().getEntries().size() == 2);
    }

}
