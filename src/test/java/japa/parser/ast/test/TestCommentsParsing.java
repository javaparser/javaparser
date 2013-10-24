package japa.parser.ast.test;

import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.Node;
import org.junit.Test;

import japa.parser.ast.CompilationUnit;

import static org.junit.Assert.*;

public class TestCommentsParsing {

  @Test
  public
  void testCompilationUnitAttributedComment() throws Exception {
      String code = "/*CompilationUnitComment*/package japa.parser.javacc;\n" +
              "public class AClass {\n" +
              "}";
      CompilationUnit cu = Helper.parserString(code);
      assertNotNull(cu.getComment());
      assertEquals("CompilationUnitComment",cu.getComment().getContent());
  }

    @Test
    public
    void testCompilationUnitNotAttributedComment() throws Exception {
        String code = "package japa.parser.javacc;/*NotCompilationUnitComment*/\n" +
                "public class AClass {\n" +
                "}";
        CompilationUnit cu = Helper.parserString(code);
        assertNull(cu.getComment());
    }


    @Test
    public
    void testDifferentCommentsForInACompilationUnit() throws Exception {
      String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineComments.java"));
      CompilationUnit cu = Helper.parserString(source);

      assertNull(cu.getComment());

      ClassOrInterfaceDeclaration clazzDecl = (ClassOrInterfaceDeclaration)cu.getChildrenNodes().get(2);

      MethodDeclaration methodDecl = (MethodDeclaration)clazzDecl.getMembers().get(0);
      BlockStmt block = methodDecl.getBody();

      assertEquals(4,block.getAllContainedComments().size());
      assertEquals(3,block.getOrphanComments().size());
      assertEquals(0,methodDecl.getOrphanComments().size());
      assertEquals(4,methodDecl.getAllContainedComments().size());
      assertEquals(4,clazzDecl.getAllContainedComments().size());

      assertEquals(4,cu.getAllContainedComments().size());

      assertEquals(0,cu.getOrphanComments().size());
    }

  @Test
  public void testNodeGetAllContainedComments() throws Exception {
      String source = Helper.readStream(getClass().getResourceAsStream("ClassWithVariousOrphanComments.java"));

      CompilationUnit cu1 = Helper.parserString(source);
      assertEquals(6,cu1.getAllContainedComments().size());

      TypeDeclaration classDecl = cu1.getTypes().get(0);
      assertEquals(4,classDecl.getAllContainedComments().size());

      MethodDeclaration methodDecl = (MethodDeclaration)classDecl.getMembers().get(0);
      assertEquals(1,methodDecl.getAllContainedComments().size());

      BlockStmt methodBody = methodDecl.getBody();
      assertEquals(1,methodBody.getAllContainedComments().size());
  }

  @Test
  public void testAgainNodeGetAllContainedComments() throws Exception {
      final String source_with_comment = //
              "package japa.parser.javacc;\n" + //
                      "public class Teste {\n" + //
                      "//line comment\n" + //
                      "int a = 0;" + //
                      "//line comment\r\n" + //
                      "int b = 0;" + //
                      "//line comment\r" + //
                      "int c = 0;" + //
                      "/* multi-line\n comment\n*/" + //
                      "int d = 0;" + //
                      "/** multi-line\r\n javadoc\n*/" + //
                      "int e = 0;" + //
                      "}\n" + //
                      "//final comment" + //
                      "";
      final CompilationUnit cu = Helper.parserString(source_with_comment);

      assertEquals(3, cu.getChildrenNodes().size());
      assertNull(cu.getChildrenNodes().get(0).getComment());
      assertEquals(0, cu.getChildrenNodes().get(0).getAllContainedComments().size());
      assertNull(cu.getChildrenNodes().get(1).getComment());
      ClassOrInterfaceDeclaration clazzDecl = (ClassOrInterfaceDeclaration)cu.getChildrenNodes().get(1);

      assertEquals(5,clazzDecl.getMembers().size());

      FieldDeclaration fieldA = (FieldDeclaration)clazzDecl.getMembers().get(0);
      assertNotNull(fieldA.getComment());
      assertEquals(0,fieldA.getAllContainedComments().size());

      FieldDeclaration fieldB = (FieldDeclaration)clazzDecl.getMembers().get(1);
      assertNotNull(fieldB.getComment());
      assertEquals(0,fieldB.getAllContainedComments().size());

      FieldDeclaration fieldC = (FieldDeclaration)clazzDecl.getMembers().get(2);
      assertNotNull(fieldC.getComment());
      assertEquals(0,fieldC.getAllContainedComments().size());

      FieldDeclaration fieldD = (FieldDeclaration)clazzDecl.getMembers().get(3);
      assertNotNull(fieldD.getComment());
      assertEquals(0,fieldD.getAllContainedComments().size());

      FieldDeclaration fieldE = (FieldDeclaration)clazzDecl.getMembers().get(4);
      assertEquals("e",fieldE.getVariables().get(0).getId().getName());
      assertNotNull(fieldE.getComment());
      assertEquals(0,fieldE.getAllContainedComments().size());

      assertEquals(5, clazzDecl.getAllContainedComments().size());
      assertEquals(6, cu.getAllContainedComments().size());

      assertEquals(1, cu.getOrphanComments().size());

  }

  @Test
  public void testAttributionOfOrphanComments() throws Exception {
      String source = Helper.readStream(getClass().getResourceAsStream("ClassWithVariousOrphanComments.java"));
      CompilationUnit cu1 = Helper.parserString(source);

      assertNull(cu1.getComment());
      assertEquals(1,cu1.getOrphanComments().size());
      assertEquals("Orphan comment inside the CompilationUnit",cu1.getOrphanComments().get(0).getContent());

      TypeDeclaration classDecl = cu1.getTypes().get(0);
      assertEquals("Javadoc associated with the class",classDecl.getComment().getContent());
      assertEquals(2, classDecl.getOrphanComments().size());
      assertEquals("a first comment floating in the class",classDecl.getOrphanComments().get(0).getContent());
      assertEquals("a second comment floating in the class",classDecl.getOrphanComments().get(1).getContent());

      MethodDeclaration methodDecl = (MethodDeclaration)classDecl.getMembers().get(0);
      assertEquals("comment associated to the method",methodDecl.getComment().getContent().trim());
      assertEquals(0,methodDecl.getOrphanComments().size());
      assertEquals("comment floating inside the method",methodDecl.getAllContainedComments().get(0).getContent());

      BlockStmt methodBody = methodDecl.getBody();
      assertEquals(1,methodBody.getOrphanComments().size());
      assertEquals("comment floating inside the method",methodBody.getOrphanComments().get(0).getContent());
  }

}
