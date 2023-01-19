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
import com.github.javaparser.ast.Modifier.Keyword;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue3358Test extends AbstractLexicalPreservingTest  {
    
    @Test
    void testArrayTypeWithBracketAfterTypeWithoutWhitespace() {
        String def = "int[] i";
        considerVariableDeclaration(def);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
        assertTrue(LexicalPreservingPrinter.print(expression).equals("private int[] i"));
    }
    
    @Test
    void testArrayTypeWithWhitespaceBeforeTypeAndBracket() {
        String def = "int [] i";
        considerVariableDeclaration(def);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
        assertTrue(LexicalPreservingPrinter.print(expression).equals("private int [] i"));
    }
    
    @Test
    void testArrayTypeWithWhitespaceBeforeEachToken() {
        String def = "int [ ] i";
        considerVariableDeclaration(def);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
        assertTrue(LexicalPreservingPrinter.print(expression).equals("private int [ ] i"));
    }
    
    @Test
    void testArrayTypeWithMultipleWhitespaces() {
        String def = "int   [   ]   i";
        considerVariableDeclaration(def);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
        assertTrue(LexicalPreservingPrinter.print(expression).equals("private int   [   ]   i"));
    }
    
// TODO This syntax {@code int i[]} does not work!
    
}
