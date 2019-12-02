/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Modifier.Keyword;
import com.github.javaparser.ast.body.EnumDeclaration;

class PrettyPrinterIssue2340Test extends AbstractLexicalPreservingTest {

    @Test
    void printingVariableDeclarationWithAddedModifier() {
        String def2 = "List i";
        considerVariableDeclaration(def2);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
    }

    @Test
    void printingGenericVariableDeclarationWithAddedModifier() {
        String def2 = "List<String> i";
        considerVariableDeclaration(def2);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
    }
    
    @Test
    void printingGenericVariableDeclarationWithAddedModifierWithAnotherSyntaxe() {
        String def2 = "List <String> i";
        considerVariableDeclaration(def2);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
    }
    
    @Test
    void printingGeneric2VariableDeclarationWithAddedModifier() {
        String def2 = "List<List<String>> i";
        considerVariableDeclaration(def2);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
    }
    
    @Test
    void printingGeneric2VariableDeclarationWithAddedModifierWithAnotherSyntaxe() {
        String def2 = "List < List < String > > i";
        considerVariableDeclaration(def2);
        expression.asVariableDeclarationExpr().getModifiers().addFirst(Modifier.privateModifier());
        assertTrue(LexicalPreservingPrinter.getOrCreateNodeText(expression).getElements().stream()
                .anyMatch(elem -> elem.expand().equals(Keyword.PRIVATE.asString())));
    }

}
