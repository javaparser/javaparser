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
