package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.body.EnumDeclaration;

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
        System.out.println(LexicalPreservingPrinter.print(cu));
        assertTrue(decl.get().getEntries().size() == 2);
    }

}
