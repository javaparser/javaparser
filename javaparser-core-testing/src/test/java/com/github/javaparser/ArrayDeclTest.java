package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.CURRENT;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class ArrayDeclTest {
    @BeforeEach
    void setToLatestJava() {
        StaticJavaParser.getConfiguration().setLanguageLevel(BLEEDING_EDGE);
    }

    @AfterEach
    void resetJavaLevel() {
        StaticJavaParser.getConfiguration().setLanguageLevel(CURRENT);
    }

    @Test
    void simple_bracket_test_back() {
        String code = "public class Test { String[] allTest; }";
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
        Optional<ClassOrInterfaceDeclaration> clazzOptional = cu.getClassByName("Test");
        assertTrue(clazzOptional.isPresent());
        ClassOrInterfaceDeclaration clazz = clazzOptional.get();
        NodeList<BodyDeclaration<?>> members = clazz.getMembers();
        members.forEach(
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
        String changed = LexicalPreservingPrinter.print(cu);
        assertEquals(changed, "public class Test { @Nullable\nString[] allTest; }");
    }

    @Test
    void simple_bracket_test_front() {
        String code = "public class Test { String allTest[]; }";
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
        Optional<ClassOrInterfaceDeclaration> clazzOptional = cu.getClassByName("Test");
        assertTrue(clazzOptional.isPresent());
        ClassOrInterfaceDeclaration clazz = clazzOptional.get();
        NodeList<BodyDeclaration<?>> members = clazz.getMembers();
        members.forEach(
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
        String changed = LexicalPreservingPrinter.print(cu);
        assertEquals(changed, "public class Test { @Nullable\nString allTest[]; }");
    }
}
