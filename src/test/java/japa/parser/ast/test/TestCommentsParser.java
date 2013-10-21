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
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(4,cc.getLineComments().size());
    }

    @Test
    public
    void testLineCommentsHaveRightContent() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineComments.java"));
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
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithLineComments.java"));
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

    @Test
    public
    void testBlockCommentsAreParsed() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithBlockComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(5,cc.getBlockComments().size());
    }

    @Test
    public
    void testBlockCommentsHaveRightContent() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithBlockComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(" comment which is not attributed to the class, it floats around as an orphan ",cc.getBlockComments().get(0).getContent());
        assertEquals(" comment to a class ",cc.getBlockComments().get(1).getContent());
        assertEquals(" comment to a method ",cc.getBlockComments().get(2).getContent());
        assertEquals(" comment put randomly in class:\n" +
                "\n" +
                "    another orphan.\n" +
                "    It spans over more lines ",cc.getBlockComments().get(3).getContent());
        assertEquals(" a comment lost inside a compilation unit. It is orphan, I am sure you got this one ",cc.getBlockComments().get(4).getContent());
    }

    @Test
    public
    void testBlockCommentsHaveRightPosition() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithBlockComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);

        assertEquals(3,cc.getBlockComments().get(0).getBeginLine());
        assertEquals(1,cc.getBlockComments().get(0).getBeginColumn());
        assertEquals(3,cc.getBlockComments().get(0).getEndLine());
        assertEquals(82,cc.getBlockComments().get(0).getEndColumn());

        assertEquals(4,cc.getBlockComments().get(1).getBeginLine());
        assertEquals(1,cc.getBlockComments().get(1).getBeginColumn());
        assertEquals(4,cc.getBlockComments().get(1).getEndLine());
        assertEquals(25,cc.getBlockComments().get(1).getEndColumn());

        assertEquals(7,cc.getBlockComments().get(2).getBeginLine());
        assertEquals(5,cc.getBlockComments().get(2).getBeginColumn());
        assertEquals(7,cc.getBlockComments().get(2).getEndLine());
        assertEquals(30,cc.getBlockComments().get(2).getEndColumn());

        assertEquals(10,cc.getBlockComments().get(3).getBeginLine());
        assertEquals(5,cc.getBlockComments().get(3).getBeginColumn());
        assertEquals(13,cc.getBlockComments().get(3).getEndLine());
        assertEquals(32,cc.getBlockComments().get(3).getEndColumn());

        assertEquals(17,cc.getBlockComments().get(4).getBeginLine());
        assertEquals(1,cc.getBlockComments().get(4).getBeginColumn());
        assertEquals(17,cc.getBlockComments().get(4).getEndLine());
        assertEquals(89,cc.getBlockComments().get(4).getEndColumn());
    }

    @Test
    public
    void testJavadocCommentsAreParsed() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithJavadocComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(2,cc.getJavadocComments().size());
    }

    @Test
    public
    void testJavadocCommentsHaveRightContent() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithJavadocComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);
        assertEquals(" a proper javadoc comment ",cc.getJavadocComments().get(0).getContent());
        assertEquals(" a floating javadoc comment ",cc.getJavadocComments().get(1).getContent());
    }

    @Test
    public
    void testJavadocCommentsHaveRightPosition() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("ClassWithJavadocComments.java"));
        CommentsParser parser = new CommentsParser();
        CommentsCollection cc = parser.parse(source);

        assertEquals(3,cc.getJavadocComments().get(0).getBeginLine());
        assertEquals(1,cc.getJavadocComments().get(0).getBeginColumn());
        assertEquals(3,cc.getJavadocComments().get(0).getEndLine());
        assertEquals(32,cc.getJavadocComments().get(0).getEndColumn());

        assertEquals(10,cc.getJavadocComments().get(1).getBeginLine());
        assertEquals(1,cc.getJavadocComments().get(1).getBeginColumn());
        assertEquals(10,cc.getJavadocComments().get(1).getEndLine());
        assertEquals(34,cc.getJavadocComments().get(1).getEndColumn());
    }

}
