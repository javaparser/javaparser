package com.github.javaparser.utils;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.comments.Comment;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.PositionUtils.nodeContains;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class PositionUtilsTest {
    @Test
    public void nodeContainsNoAnnotationsAnywhereIgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        boolean contains = nodeContains(cu, field, true);

        assertTrue(contains);
    }

    @Test
    public void nodeDoesNotContainNoAnnotationsAnywhereIgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        boolean contains = nodeContains(field.getVariable(0).getType(), field.getVariable(0).getName(), true);

        assertFalse(contains);
    }

    @Test
    public void nodeContainsNoAnnotationsAnywhere() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        boolean contains = nodeContains(cu, field, false);

        assertTrue(contains);
    }

    @Test
    public void nodeDoesNotContainNoAnnotationsAnywhere() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        boolean contains = nodeContains(field.getVariable(0).getType(), field.getVariable(0).getName(), false);

        assertFalse(contains);
    }

    @Test
    public void nodeContainsAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("@A class X {} class Y {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        ClassOrInterfaceDeclaration y = cu.getClassByName("Y").get();

        boolean contains = nodeContains(x, y, true);

        assertFalse(contains);
    }

    @Test
    public void nodeContainsAnnotationsWithCommentNodeInTheMiddle() {
        CompilationUnit cu = StaticJavaParser.parse("@A /*o*/ @B class X {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        Comment o = x.getAnnotationByName("B").get().getComment().get();

        boolean contains = nodeContains(x, o, true);

        assertFalse(contains);
    }

    @Test
    public void nodeContainsAnnotationsWithCommentAtTheEnd() {
        CompilationUnit cu = StaticJavaParser.parse("@A @B /*o*/ public class X {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        Comment o = x.getName().getComment().get();

        boolean contains = nodeContains(x, o, true);

        assertTrue(contains);
    }

    @Test
    public void nodeContainsAnnotationsWithCommentAfterTheEnd() {
        CompilationUnit cu = StaticJavaParser.parse("@A @B public /*o*/ class X {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        Comment o = x.getName().getComment().get();

        boolean contains = nodeContains(x, o, true);

        assertTrue(contains);
    }
}
