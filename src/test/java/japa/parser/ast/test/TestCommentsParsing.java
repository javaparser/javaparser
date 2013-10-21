package japa.parser.ast.test;

import japa.parser.ast.LineComment;
import japa.parser.ast.Node;
import japa.parser.ast.TreeVisitor;
import japa.parser.ast.visitor.VoidVisitorAdapter;
import org.junit.Test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.visitor.CloneVisitor;
import japa.parser.ast.visitor.GenericVisitorAdapter;

import java.util.List;
import java.util.LinkedList;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class TestCommentsParsing {

  private static class CommentsCollector extends TreeVisitor {
      List<LineComment> lineComments = new LinkedList<LineComment>();

      @Override
      public void process(Node node) {
          if (node instanceof  LineComment){
              lineComments.add((LineComment)node);
          }
      }
  }

  @Test
  public
  void testCommentsAboveStatements() throws Exception {
      String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineComments.java"));
      CompilationUnit cu1 = Helper.parserString(source);
      CommentsCollector cc = new CommentsCollector();
      cc.visitDepthFirst(cu1);
      assertEquals(4,cc.lineComments.size());
  }

}
