package japa.parser.ast.test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.comments.BlockComment;
import japa.parser.ast.comments.Comment;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.expr.IntegerLiteralExpr;
import japa.parser.ast.expr.VariableDeclarationExpr;
import japa.parser.ast.stmt.ExpressionStmt;
import japa.parser.ast.test.Helper;
import japa.parser.ast.type.PrimitiveType;
import japa.parser.ast.type.ReferenceType;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Tests to verify the correctness of the samples on parsing
 * shown on the wiki, currently at https://github.com/matozoid/javaparser/wiki/CommentsParsing
 *
 * @author ftomassetti
 * @since July 2014
 */
public class TestWikiSamplesOnComments {

    @Test
    public void testClassWithSingleOrphanComment() throws Exception {
        String source = "class A {\n" +
                "  // orphan comment\n" +
                "}";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());
        Comment onlyComment = cu.getAllContainedComments().get(0);
        assertTrue(onlyComment.isOrphan());
        assertTrue(onlyComment.getParentNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Test
    public void testClassWithSingleComment() throws Exception {
        String source = "/* Comment of the class */\n" +
                "class A { }";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());
        Comment onlyComment = cu.getAllContainedComments().get(0);
        assertFalse(onlyComment.isOrphan());
        assertTrue(onlyComment.getCommentedNode() instanceof ClassOrInterfaceDeclaration);
        assertTrue(onlyComment.getParentNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Test
    public void testClassWithTwoComments() throws Exception {
        String source = "/* Orphan comment */\n" +
                "/* Comment of the class */\n" +
                "class A { }";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(2, cu.getAllContainedComments().size());
        Comment orphanComment = cu.getAllContainedComments().get(0);
        assertEquals(" Orphan comment ", orphanComment.getContent());
        assertTrue(orphanComment.isOrphan());

        Comment classComment = cu.getAllContainedComments().get(1);
        assertEquals(" Comment of the class ", classComment.getContent());
        assertFalse(classComment.isOrphan());
        assertTrue(classComment.getCommentedNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Test
    public void testCommentAssociatedToAField() throws Exception {
        String source = "class A {\n"
                        +"   int a = 0; // comment associated to the field\n"
                        +"}";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());
        Comment onlyComment = cu.getAllContainedComments().get(0);
        assertFalse(onlyComment.isOrphan());
        assertTrue(onlyComment.getCommentedNode() instanceof FieldDeclaration);
    }

    @Test
    public void testCommentAssociatedToAFieldInitializationValue() throws Exception {
        String source = "class A {\n"
                +"   int a \n"
                +"          = 0; // comment associated to the field\n"
                +"}";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());
        Comment onlyComment = cu.getAllContainedComments().get(0);
        assertFalse(onlyComment.isOrphan());
        assertTrue(onlyComment.getCommentedNode() instanceof IntegerLiteralExpr);
    }

    @Test
    public void testInteractionBetweenOneInlineAndOneBlocComment() throws Exception {
        String source = "class A {\n"
                + "   void foo() {\n"
                + "      // a comment\n"
                + "        int b; // another comment\n"
                + "   }\n"
                + "}";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(2, cu.getAllContainedComments().size());

        Comment comment1 = cu.getAllContainedComments().get(0);
        assertEquals(" a comment", comment1.getContent());
        assertTrue(comment1.isOrphan());

        Comment comment2 = cu.getAllContainedComments().get(1);
        assertEquals(" another comment", comment2.getContent());
        assertFalse(comment2.isOrphan());
        // variable declaration are expression statement
        assertTrue(comment2.getCommentedNode() instanceof ExpressionStmt);
        assertTrue(((ExpressionStmt)comment2.getCommentedNode()).getExpression() instanceof VariableDeclarationExpr);
    }

    @Test
    public void testAnInlineCommentInsideABlockComment() throws Exception {
        String source = "class A {\n"
                + "  /* A block comment that \n" +
                "    // Contains a line comment\n" +
                "    */\n" +
                "    public static void main(String args[]) {\n" +
                "    }\n"
                + "}";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());

        Comment comment1 = cu.getAllContainedComments().get(0);
        assertEquals(" A block comment that \n" +
                "    // Contains a line comment\n" +
                "    ", comment1.getContent());
        assertTrue(comment1 instanceof BlockComment);
    }

    @Test
    public void testCommentsAttributionForCommentsAfterAnntations() throws Exception {
        String source = "class A {\n"
                + "  @Override\n" +
                "    // Returns number of vowels in a name\n" +
                "    public int countVowels(String name) {\n" +
                "    }\n"
                + "}";
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());

        Comment comment1 = cu.getAllContainedComments().get(0);
        assertTrue(comment1.getCommentedNode() instanceof PrimitiveType);
        assertEquals(PrimitiveType.Primitive.Int, ((PrimitiveType)comment1.getCommentedNode()).getType());
    }
}
