package japa.parser.ast.test;

import japa.parser.ast.LineComment;
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

  private static class CommentsCollector extends VoidVisitorAdapter<Object> {
    private List<LineComment> lineComments = new LinkedList<LineComment>();

    public List<LineComment> getLineComments(){
        return lineComments;
    }

    public void visit(final LineComment n, final Object arg) {
        System.out.println("VISITING '"+n.getContent()+"'");
        lineComments.add(n);
    }
  }

  @Test
  public
  void testCommentsAboveStatements() throws Exception {
      String source = Helper.readStream(getClass().getResourceAsStream("ClassWithComments.java"));
      CompilationUnit cu1 = Helper.parserString(source);
      CommentsCollector cc = new CommentsCollector();
      cu1.accept(cc,"");
      assertEquals(4,cc.getLineComments().size());
  }

}
