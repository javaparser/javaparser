/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.utils;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.PositionUtils.nodeContains;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.*;

public class PositionUtilsTest {
    @Test
    public void nodeContains_NoAnnotationsAnywhere_IgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        boolean contains = nodeContains(cu, field, true);
        assertTrue(contains);
    }

    @Test
    public void nodeDoesNotContain_NoAnnotationsAnywhere_IgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        Type fieldType = field.getVariable(0).getType();
        SimpleName fieldName = field.getVariable(0).getName();

        boolean contains = nodeContains(fieldType, fieldName, true);
        assertFalse(contains);
    }

    @Test
    public void nodeContains_NoAnnotationsAnywhere_IncludeAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        boolean contains = nodeContains(cu, field, false);
        assertTrue(contains);
    }

    @Test
    public void nodeDoesNotContain_NoAnnotationsAnywhere_IncludeAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("class X { int a; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        Type fieldType = field.getVariable(0).getType();
        SimpleName fieldName = field.getVariable(0).getName();

        boolean contains = nodeContains(fieldType, fieldName, false);
        assertFalse(contains, "Type and Name are separate branches of the AST, thus should not contain each other.");
    }

    @Test
    public void nodeContainsAnnotations_IgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("@A class X {} class Y {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        ClassOrInterfaceDeclaration y = cu.getClassByName("Y").get();

        boolean contains = nodeContains(x, y, true);
        assertFalse(contains);
    }

    @Test
    public void nodeContainsAnnotations_WithCommentNodeInTheMiddle_IgnoringAnnotations() {
        String code = "" +
                "@A\n" +
                "/*o*/\n" +
                "@B\n" +
                "class X {\n" +
                "}\n" +
                "";

        CompilationUnit cu = StaticJavaParser.parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString(), "Issue with the parsing of the code, not this test.");

        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        AnnotationExpr annotationB = x.getAnnotationByName("B").get();

        // Comment gets added to the MarkerAnnotationExpr for @B -- correct
        Comment o = annotationB.getComment().get();
        assertEquals(annotationB, o.getCommentedNode().get(), "Comment has been added to an unexpected node.");

        boolean contains = nodeContains(x, o, true);
        assertFalse(contains);
    }


    @Test
    public void nodeContainsAnnotations_WithAnnotationNodeInTheMiddle() {
        String code = "" +
                "@A\n" +
                "@B\n" +
                "@C\n" +
                "class X {\n" +
                "}\n" +
                "";
        CompilationUnit cu = StaticJavaParser.parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString(), "Issue with the parsing of the code, not this test.");

        final ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();
        final AnnotationExpr annotationA = x.getAnnotationByName("A").get();
        final AnnotationExpr annotationB = x.getAnnotationByName("B").get();
        final AnnotationExpr annotationC = x.getAnnotationByName("C").get();

        // If including annotations (i.e. NOT ignoring them), all nodes should be included
        assertTrue(nodeContains(x, annotationA, false), formatRangeCompareResult(x, annotationA, "X", "A"));
        assertTrue(nodeContains(x, annotationB, false), formatRangeCompareResult(x, annotationB, "X", "B"));
        assertTrue(nodeContains(x, annotationC, false), formatRangeCompareResult(x, annotationC, "X", "C"));
        assertTrue(nodeContains(x, x, false), formatRangeCompareResult(x, x, "X", "X"));

        // If ignoring annotations, only the node itself should be included
        assertFalse(nodeContains(x, annotationA, true), formatRangeCompareResult(x, annotationA, "X", "A"));
        assertFalse(nodeContains(x, annotationB, true), formatRangeCompareResult(x, annotationB, "X", "B"));
        assertFalse(nodeContains(x, annotationC, true), formatRangeCompareResult(x, annotationC, "X", "C"));
        assertFalse(nodeContains(x, x, true), formatRangeCompareResult(x, x, "X", "X"));

    }

    private String formatRangeCompareResult(Node x, Node annotationA, String containerId, String otherId) {
        return String.format("container range in detected as NOT containing other range: " +
                        "\n - container (%s): %s" +
                        "\n -     other (%s): %s",
                containerId,
                x.getRange().get().toString(),
                otherId,
                annotationA.getRange().get().toString()
        );
    }

    @Test
    public void nodeContainsAnnotations_WithCommentAtTheEndOfAnnotations_IgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("@A @B /*o*/ public class X {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();

        // TODO: Should the comment be attached to the SimpleName (as opposed to the ClassOrInterfaceDeclaration?)
        SimpleName simpleName = x.getName();
        Comment o = simpleName.getComment().get();

        //// 0        1         2         2
        //// 123456789012345678901234567890
        //// @A @B /*o*/ public class X {}
        //// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ // range of x, WITH annotations -- thus contained == TRUE
        //// @A @B /*o*/ public class X {}
        ////             ^^^^^^^^^^^^^^^^^ // range of x, ignoring annotations -- thus contained == FALSE
        //// @A @B /*o*/ public class X {}
        ////       ^^^^^                   // range of o

        // TODO: Determine if comments outside the text range of a node are "contained" within a node (part of the subtree, but are printed before).
        assertTrue(nodeContains(x, o, false), formatRangeCompareResult(x, o, "X", "o"));
        assertFalse(nodeContains(x, o, true), formatRangeCompareResult(x, o, "X", "o"));


        // FIXME: Both tests currently fail due to the comment being attached to the SimpleName, as opposed to the ClassOrInterfaceDeclaration
//        assertEquals(x.getClass(), o.getCommentedNode().get().getClass(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");
//        assertEquals(x, o.getCommentedNode().get(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");

    }

    @Test
    public void nodeContainsAnnotations_WithCommentAfterTheEnd_IgnoringAnnotations() {
        CompilationUnit cu = StaticJavaParser.parse("@A @B public /*o*/ class X {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();

        // TODO: Should the comment be attached to the SimpleName (as opposed to the ClassOrInterfaceDeclaration?)
        SimpleName simpleName = x.getName();
        Comment o = simpleName.getComment().get();

        //// 0        1         2         2
        //// 123456789012345678901234567890
        //// @A @B public /*o*/ class X {}
        //// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ // range of x, WITH annotations -- thus contained == TRUE
        //// @A @B public /*o*/ class X {}
        ////       ^^^^^^^^^^^^^^^^^^^^^^^ // range of x, ignoring annotations -- thus contained == TRUE
        //// @A @B public /*o*/ class X {}
        ////              ^^^^^            // range of o

        // TODO: Determine if comments outside the text range of a node are "contained" within a node (part of the subtree, but are printed before).
        assertTrue(nodeContains(x, o, false), formatRangeCompareResult(x, o, "X", "o"));
        assertTrue(nodeContains(x, o, true), formatRangeCompareResult(x, o, "X", "o"));

        // FIXME: Both tests currently fail due to the comment being attached to the SimpleName, as opposed to the ClassOrInterfaceDeclaration
//        assertEquals(x.getClass(), o.getCommentedNode().get().getClass(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");
//        assertEquals(x, o.getCommentedNode().get(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");

    }

    @Test
    public void nodeContainsAnnotations_WithCommentAfterTheEnd_IgnoringAnnotations2() {
        CompilationUnit cu = StaticJavaParser.parse("@A @B public class /*o*/ X {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();

        // TODO: Should the comment be attached to the SimpleName (as opposed to the ClassOrInterfaceDeclaration?)
        SimpleName simpleName = x.getName();
        Comment o = simpleName.getComment().get();


        //// 12345678912345678912345678901
        //// @A @B public class /*o*/ X {}
        //// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ // range of x, WITH annotations -- thus contained == TRUE
        //// @A @B public class /*o*/ X {}
        ////       ^^^^^^^^^^^^^^^^^^^^^^^ // range of x, ignoring annotations -- thus contained == TRUE
        //// @A @B public class /*o*/ X {}
        ////                    ^^^^^      // range of o

        // TODO: Determine if comments outside the text range of a node are "contained" within a node (part of the subtree, but are printed before).
        assertTrue(nodeContains(x, o, false), formatRangeCompareResult(x, o, "X", "o"));
        assertTrue(nodeContains(x, o, true), formatRangeCompareResult(x, o, "X", "o"));

        assertTrue(o.getCommentedNode().isPresent());

        // FIXME: Both tests currently fail due to the comment being attached to the SimpleName, as opposed to the ClassOrInterfaceDeclaration
//        assertEquals(x.getClass(), o.getCommentedNode().get().getClass(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");
//        assertEquals(x, o.getCommentedNode().get(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");

    }

    @Test
    public void nodeContainsAnnotations_WithCommentAfterTheEnd_IgnoringAnnotations3() {
        CompilationUnit cu = StaticJavaParser.parse("@A @B public class X /*o*/ {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();

//        // TODO: At what point is the declaration supposed to end and the code block begin? Should the block comment move "inside" the code block?
//        // cu =
//        @A
//        @B
//        public class X {
//            /*o*/
//        }

        // TODO: Should the comment be attached to the SimpleName (as opposed to being attached to null but not orphaned?)
        Comment o = cu.getComments().get(0);


        //// 12345678912345678912345678901
        //// @A @B public class X /*o*/ {}
        //// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ // range of x, WITH annotations -- thus contained == TRUE
        //// @A @B public class X /*o*/ {}
        ////       ^^^^^^^^^^^^^^^^^^^^^^^ // range of x, ignoring annotations -- thus contained == TRUE
        //// @A @B public class X /*o*/ {}
        ////                      ^^^^^    // range of o

        // TODO: Determine if comments outside the text range of a node are "contained" within a node (part of the subtree, but are printed before).
        assertTrue(nodeContains(x, o, false), formatRangeCompareResult(x, o, "X", "o"));
        assertTrue(nodeContains(x, o, true), formatRangeCompareResult(x, o, "X", "o"));

        // FIXME: Comment is unattached (returns null), but is not considered to be orphaned...?
//        assertTrue(o.getCommentedNode().isPresent());

        // FIXME: Both tests currently fail due to the comment being unattached, as opposed to the ClassOrInterfaceDeclaration
//        assertEquals(x.getClass(), o.getCommentedNode().get().getClass(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");
//        assertEquals(x, o.getCommentedNode().get(), "Comment attached to an unexpected node -- expected to be the ClassOrInterfaceDeclaration");

    }
}
