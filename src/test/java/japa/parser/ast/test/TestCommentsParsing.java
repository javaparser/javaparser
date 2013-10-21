package japa.parser.ast.test;

import japa.parser.ast.LineComment;
import japa.parser.ast.Node;
import japa.parser.ast.TreeVisitor;
import japa.parser.ast.body.BodyDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.visitor.VoidVisitorAdapter;
import org.junit.Test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.visitor.CloneVisitor;
import japa.parser.ast.visitor.GenericVisitorAdapter;

import java.util.List;
import java.util.LinkedList;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;

public class TestCommentsParsing {

  @Test
  public
  void testDifferentCommentsForInACompilationUnit() throws Exception {
      String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineComments.java"));
      CompilationUnit cu1 = Helper.parserString(source);

      assertNull(cu1.getComment());

      assertEquals(4,cu1.getAllContainedComments().size());

      assertEquals(0,cu1.getOrphanComments().size());
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
