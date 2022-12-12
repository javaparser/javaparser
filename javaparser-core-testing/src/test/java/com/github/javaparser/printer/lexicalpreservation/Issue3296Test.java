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
