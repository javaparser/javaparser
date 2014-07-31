package japa.parser.comments;

import fixture.Helper;
import japa.parser.JavaParser;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.*;
import japa.parser.ast.comments.Comment;
import japa.parser.ast.expr.Expression;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.type.Type;
import org.junit.Test;

import static org.junit.Assert.*;

public class TestCommentsParsing {


    @Test
    public void testOrphanCommentInsideClassDecl() throws Exception {
        final String originalSource = "class /*Comment1*/ A {\n" +
                "   //comment2\n" +
                "    // comment3\n" +
                "    int a;\n" +
                "    /**comment4\n" +
                "     * \n" +
                "     * */\n" +
                "//comment5    \n" +
                " }";
        final CompilationUnit cu = Helper.parserString(originalSource);
        ClassOrInterfaceDeclaration classDecl = (ClassOrInterfaceDeclaration) cu.getTypes().get(0);
        assertNull(classDecl.getComment());
        assertEquals("Comment1", classDecl.getOrphanComments().get(0).getContent());
    }

    @Test
    public void testClassDeclComment() throws Exception {
        final String originalSource = "/*Comment1*/class A {\n" +
                "   //comment2\n" +
                "    // comment3\n" +
                "    int a;\n" +
                "    /**comment4\n" +
                "     * \n" +
                "     * */\n" +
                "//comment5    \n" +
                " }";
        final CompilationUnit cu = Helper.parserString(originalSource);
        ClassOrInterfaceDeclaration classDecl = (ClassOrInterfaceDeclaration) cu.getTypes().get(0);
        assertNotNull(classDecl.getComment());
        assertEquals("Comment1", classDecl.getComment().getContent());
    }

    @Test
    public void testSameCommentsInACompilationUnit() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineCommentsInMultipleMethods.java"));
        CompilationUnit cu = Helper.parserString(source);

        assertNull(cu.getComment());

        ClassOrInterfaceDeclaration clazzDecl = (ClassOrInterfaceDeclaration) cu.getChildrenNodes().get(2);

        MethodDeclaration methodDecl = (MethodDeclaration) clazzDecl.getMembers().get(0);
        assertEquals("aMethod",methodDecl.getName());
        BlockStmt block = methodDecl.getBody();

        assertEquals(4, block.getAllContainedComments().size());
        assertEquals(3, block.getOrphanComments().size());
        assertEquals(0, methodDecl.getOrphanComments().size());
        assertEquals(4, methodDecl.getAllContainedComments().size());

        MethodDeclaration methodDec2 = (MethodDeclaration) clazzDecl.getMembers().get(1);
        block = methodDec2.getBody();

        assertEquals(5, block.getAllContainedComments().size());
        assertEquals(4, block.getOrphanComments().size());
        assertEquals(0, methodDec2.getOrphanComments().size());
        assertEquals(5, methodDec2.getAllContainedComments().size());

        assertEquals(9, clazzDecl.getAllContainedComments().size());
        assertEquals(9, cu.getAllContainedComments().size());
        assertEquals(0, cu.getOrphanComments().size());
    }

    @Test
    public void testLineCommentInsideBlockComment() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineCommentInsideBlockComment.java"));
        CompilationUnit cu = Helper.parserString(source);

        ClassOrInterfaceDeclaration clazzDec = (ClassOrInterfaceDeclaration) cu.getChildrenNodes().get(1);
        MethodDeclaration fooMethod = (MethodDeclaration) clazzDec.getMembers().get(0);

        assertEquals("comment to a method", fooMethod.getComment().getContent().trim());

        assertEquals("// Line Comment put immediately after block comment\n" +
                "\n" +
                "    //// Comment debauchery\n" +
                "\n" +
                "    another orphan.\n" +
                "    It spans over more lines", clazzDec.getOrphanComments().get(0).getContent().trim());
    }

    @Test
    public void testIssue43AttributionOfLineCommentsToFieldValue() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("Issue43.java"));

        CompilationUnit cu = Helper.parserString(source);
        // All the comments are parsed
        assertEquals(4, cu.getAllContainedComments().size());

        ClassOrInterfaceDeclaration clazzDecl = (ClassOrInterfaceDeclaration) cu.getChildrenNodes().get(1);
        // All the comments are inside the class
        assertEquals(4, clazzDecl.getAllContainedComments().size());

        FieldDeclaration field1 = (FieldDeclaration)clazzDecl.getMembers().get(0);
        FieldDeclaration field2 = (FieldDeclaration)clazzDecl.getMembers().get(1);
        // The fields do not contain the comments
        assertEquals(0, field1.getAllContainedComments().size());
        assertEquals(0, field1.getAllContainedComments().size());

        // The comment "//Case 1" is orphan, because the field1 has already the comment following it
        // and each node can have just one comment
        assertEquals(1, clazzDecl.getOrphanComments().size());
        assertEquals("Case 1", clazzDecl.getOrphanComments().get(0).getContent());

        // The first comment is assigned to field1
        assertTrue(field1.hasComment());
        assertEquals("field1", field1.getComment().getContent());
        //System.out.println("Field1 "+field1);
        //System.out.println("Field2 "+field2);

        // The comment "Case 2" is not assegned to field1
        assertTrue(field2.hasComment());
        assertEquals("Case 2", field2.getComment().getContent());

        // The comment "field2" is assigned to "null"
        VariableDeclarator vd2 = field2.getVariables().get(0);
        Expression valueField2 = vd2.getInit();
        assertTrue(valueField2.hasComment());
        assertEquals("field2",valueField2.getComment().getContent());
    }

    @Test
    public void testIssue43VariantAttributionOfLineCommentsToFieldValue() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("Issue43variant.java"));

        CompilationUnit cu = Helper.parserString(source);
        // Both the comments are parsed
        assertEquals(2, cu.getAllContainedComments().size());

        ClassOrInterfaceDeclaration clazzDecl = (ClassOrInterfaceDeclaration) cu.getChildrenNodes().get(1);
        // Both the comments are inside the class
        assertEquals(2, clazzDecl.getAllContainedComments().size());

        FieldDeclaration field1 = (FieldDeclaration)clazzDecl.getMembers().get(0);
        FieldDeclaration field2 = (FieldDeclaration)clazzDecl.getMembers().get(1);
        // The fields do not contain the comments
        assertEquals(0, field1.getAllContainedComments().size());
        assertEquals(0, field1.getAllContainedComments().size());

        // The first comment is assigned to field1
        assertTrue(field1.hasComment());
        assertEquals("field1", field1.getComment().getContent());

        // The second comment is not assegned to field1
        assertFalse(field2.hasComment());
        // It is assigned to "null"
        VariableDeclarator vd2 = field2.getVariables().get(0);
        Expression valueField2 = vd2.getInit();
        assertTrue(valueField2.hasComment());
        assertEquals("field2",valueField2.getComment().getContent());
    }

    @Test
    public void testCorrectAttributionOfLineComments() throws Exception
    {
        final String source = //
                "package japa.parser.javacc;\n" + //
                        "public class Teste {\n" + //
                        "//line comment1 \n" + //
                        "int a = 0;//line comment2  \r\n" + //
                        "int b = 0;//line comment3 \r" + //
                        "int c = 0;/* multi-line\n comment\n*/" + //
                        "int d = 0;/** multi-line\r\n javadoc\n*/" + //
                        "int e = 0;" + //
                        "}\n" + //
                        "//final comment" + //
                        "";

        CompilationUnit cu = Helper.parserString(source);
        // All the comments are parsed
        assertEquals(6, cu.getAllContainedComments().size());

        ClassOrInterfaceDeclaration clazzDecl = (ClassOrInterfaceDeclaration) cu.getChildrenNodes().get(1);
        // Five of the comments are inside the class
        assertEquals(5, clazzDecl.getAllContainedComments().size());

        // comment1 remains orphan
        assertEquals(1, clazzDecl.getOrphanComments().size());
        assertEquals("line comment1", clazzDecl.getOrphanComments().get(0).getContent().trim());

        // Field A: it takes comment2 because it is on the same line
        FieldDeclaration fieldA = (FieldDeclaration)clazzDecl.getMembers().get(0);
        assertEquals("a", fieldA.getVariables().get(0).getId().getName());
        assertTrue(fieldA.hasComment());
        assertEquals("line comment2", fieldA.getComment().getContent().trim());

        // Field B: it takes comment3 because it is on the same line
        FieldDeclaration fieldB = (FieldDeclaration)clazzDecl.getMembers().get(1);
        assertEquals("b", fieldB.getVariables().get(0).getId().getName());
        assertTrue(fieldB.hasComment());
        assertEquals("line comment3", fieldB.getComment().getContent().trim());

        // Field C: it takes no comments
        FieldDeclaration fieldC = (FieldDeclaration)clazzDecl.getMembers().get(2);
        assertEquals("c", fieldC.getVariables().get(0).getId().getName());
        assertFalse(fieldC.hasComment());
    }

    @Test
    public void testFollowedByEmptyLinesAreOrphan() throws Exception {
        String sourceWithEmptyLine = "//comment\n"
                + "   \n"
                +"class A {}";
        String sourceWithoutEmptyLine = "//comment\n"
                +"class A {}";

        CompilationUnit cuWithEmptyLine = Helper.parserString(sourceWithEmptyLine);
        Comment commentBeforeEmptyLine = cuWithEmptyLine.getAllContainedComments().get(0);
        assertTrue(commentBeforeEmptyLine.isOrphan());

        CompilationUnit cuWithoutEmptyLine = Helper.parserString(sourceWithoutEmptyLine);
        Comment commentBeforeNotEmptyLine = cuWithoutEmptyLine.getAllContainedComments().get(0);
        assertFalse(commentBeforeNotEmptyLine.isOrphan());
        assertTrue(commentBeforeNotEmptyLine.getCommentedNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Test
    public void testIssue40CommentsAfterJavadocAreAttributedToTheMethodIfFlagIsActive() throws Exception {
        String source = "class A{\n"+
                        "  @GET\n" +
                        "  @Path(\"/original\")\n" +
                        "  /**\n" +
                        "   * Return the original user.\n" +
                        "   */\n" +
                        "  public User getOriginalUser(String userName) {\n" +
                        "      return userService.getOriginalUser(userName);\n" +
                        "  }\n"+
                        "}";
        JavaParser.setDoNotConsiderAnnotationsAsNodeStartForCodeAttribution(true);
        try {
            CompilationUnit cu = Helper.parserString(source);
            assertEquals(1, cu.getAllContainedComments().size());
            Comment comment = cu.getAllContainedComments().get(0);
            assertFalse(comment.isOrphan());
            assertTrue(comment.getCommentedNode() instanceof MethodDeclaration);
        } finally {
            JavaParser.setDoNotConsiderAnnotationsAsNodeStartForCodeAttribution(false);
        }
    }

    @Test
    public void testIssue40CommentsAfterJavadocAreAttributedToTheMethodIfFlagIsNotActive() throws Exception {
        String source = "class A{\n"+
                "  @GET\n" +
                "  @Path(\"/original\")\n" +
                "  /**\n" +
                "   * Return the original user.\n" +
                "   */\n" +
                "  public User getOriginalUser(String userName) {\n" +
                "      return userService.getOriginalUser(userName);\n" +
                "  }\n"+
                "}";
        JavaParser.setDoNotConsiderAnnotationsAsNodeStartForCodeAttribution(false);
        CompilationUnit cu = Helper.parserString(source);
        assertEquals(1, cu.getAllContainedComments().size());
        Comment comment = cu.getAllContainedComments().get(0);
        assertFalse(comment.isOrphan());
        assertTrue(comment.getCommentedNode() instanceof Type);
    }

}
