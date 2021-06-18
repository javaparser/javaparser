package com.github.javaparser.issues;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.CURRENT;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class Issue3296Test {

    private ClassOrInterfaceDeclaration getClass(CompilationUnit cu, String className){
        Optional<ClassOrInterfaceDeclaration> clazzOptional = cu.getClassByName(className);
        assertTrue(clazzOptional.isPresent());
        return clazzOptional.get();
    }

    private void applyFieldAnnot(ClassOrInterfaceDeclaration clazz, String fieldName, String annot) {
        clazz.getMembers().forEach(
                bodyDeclaration ->
                        bodyDeclaration.ifFieldDeclaration(
                                fieldDeclaration -> {
                                    NodeList<VariableDeclarator> vars =
                                            fieldDeclaration.asFieldDeclaration().getVariables();
                                    for (VariableDeclarator v : vars) {
                                        if (v.getName().toString().equals(fieldName)) {
                                            fieldDeclaration.addMarkerAnnotation(annot);
                                            break;
                                        }
                                    }
                                }));
    }


    @BeforeEach
    void setToLatestJava() {
        StaticJavaParser.getConfiguration().setLanguageLevel(BLEEDING_EDGE);
    }

    @AfterEach
    void resetJavaLevel() {
        StaticJavaParser.getConfiguration().setLanguageLevel(CURRENT);
    }

    @Test
    void single_bracket_test_back() {
        String code = "public class Test { String[] allTest; }";
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
        ClassOrInterfaceDeclaration clazz = getClass(cu, "Test");
        applyFieldAnnot(clazz, "allTest", "Nullable");
        String changed = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(changed, "public class Test { @Nullable\nString[] allTest; }");
    }

    @Test
    void single_bracket_test_front() {
        String code = "public class Test { String allTest[]; }";
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
        ClassOrInterfaceDeclaration clazz = getClass(cu, "Test");
        applyFieldAnnot(clazz, "allTest", "Nullable");
        String changed = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(changed, "public class Test { @Nullable\nString allTest[]; }");
    }

    @Test
    void multiple_bracket_test_back() {
        String code = "public class A {\n\tString[] allTest;\n\tObject[] allObjects;\n}\nclass B {\n\tString[] allTest;\n}";
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
        ClassOrInterfaceDeclaration clazzA = getClass(cu, "A");
        applyFieldAnnot(clazzA, "allTest", "Nullable");
        applyFieldAnnot(clazzA, "allObjects", "Null");
        ClassOrInterfaceDeclaration clazzB = getClass(cu, "B");
        applyFieldAnnot(clazzB, "allTest", "NotNull");
        String changed = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(changed, "public class A {\n\t@Nullable\n\tString[] allTest;\n\t@Null\n\tObject[] allObjects;\n}\nclass B {\n\t@NotNull\n\tString[] allTest;\n}");
    }

    @Test
    void multiple_bracket_test_front() {
        String code = "public class A {\n\tString allTest[];\n\tObject allObjects[];\n}\nclass B {\n\tString allTest[];\n}";
        CompilationUnit cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
        ClassOrInterfaceDeclaration clazzA = getClass(cu, "A");
        applyFieldAnnot(clazzA, "allTest", "Nullable");
        applyFieldAnnot(clazzA, "allObjects", "Null");
        ClassOrInterfaceDeclaration clazzB = getClass(cu, "B");
        applyFieldAnnot(clazzB, "allTest", "NotNull");
        String changed = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(changed, "public class A {\n\t@Nullable\n\tString allTest[];\n\t@Null\n\tObject allObjects[];\n}\nclass B {\n\t@NotNull\n\tString allTest[];\n}");
    }
}
