package japa.parser.ast.test;

import japa.parser.ast.comments.CommentsCollection;
import japa.parser.ast.comments.CommentsParser;
import org.junit.Test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.visitor.CloneVisitor;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class TestCommentsParser {

    @Test
    public
    void testLineCommentsAreParsed() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(4,cc.getLineComments().size());
    }

    @Test
    public
    void testLineCommentsHaveRightContent() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(" first comment",cc.getLineComments().get(0).getContent());
        assertEquals("second comment",cc.getLineComments().get(1).getContent());
        assertEquals(" third comment",cc.getLineComments().get(2).getContent());
        assertEquals(" fourth comment",cc.getLineComments().get(3).getContent());
    }

    @Test
    public
    void testLineCommentsHaveRightPosition() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);

        assertEquals(9,cc.getLineComments().get(0).getBeginLine());
        assertEquals(5,cc.getLineComments().get(0).getBeginColumn());
        assertEquals(9,cc.getLineComments().get(0).getEndLine());
        assertEquals(21,cc.getLineComments().get(0).getEndColumn());

        assertEquals(10,cc.getLineComments().get(1).getBeginLine());
        assertEquals(14,cc.getLineComments().get(1).getBeginColumn());
        assertEquals(10,cc.getLineComments().get(1).getEndLine());
        assertEquals(30,cc.getLineComments().get(1).getEndColumn());

        assertEquals(11,cc.getLineComments().get(2).getBeginLine());
        assertEquals(5,cc.getLineComments().get(2).getBeginColumn());
        assertEquals(11,cc.getLineComments().get(2).getEndLine());
        assertEquals(21,cc.getLineComments().get(2).getEndColumn());

        assertEquals(12,cc.getLineComments().get(3).getBeginLine());
        assertEquals(5,cc.getLineComments().get(3).getBeginColumn());
        assertEquals(12,cc.getLineComments().get(3).getEndLine());
        assertEquals(22,cc.getLineComments().get(3).getEndColumn());
    }

}
