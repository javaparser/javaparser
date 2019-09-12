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
