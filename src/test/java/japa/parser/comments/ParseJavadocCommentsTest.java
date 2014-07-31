package japa.parser.comments;

import fixture.Helper;
import japa.parser.ast.comments.CommentsCollection;
import japa.parser.ast.comments.CommentsParser;
import japa.parser.ast.comments.JavadocComment;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.is;


public class ParseJavadocCommentsTest {

    private CommentsCollection commentsCollection;
    private JavadocComment firstComment;
    private JavadocComment secondComment;

    private static final String CLASS_WITH_JAVADOC_COMMENTS_FILE = "ClassWithJavadocComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_JAVADOC_COMMENTS_FILE));
        commentsCollection = new CommentsParser().parse(source);

        firstComment = commentsCollection.getJavadocComments().get(0);
        secondComment = commentsCollection.getJavadocComments().get(1);
    }

    @Test
    public void testJavadocCommentsAreParsed() throws Exception {

        assertThat(commentsCollection.size(), is(2));
    }

    @Test
    public void testJavadocCommentsHaveRightContent() throws Exception {

        assertThat(firstComment.getContent(), is(" a proper javadoc comment "));
        assertThat(secondComment.getContent(), is(" a floating javadoc comment "));
    }

    @Test
    public void testJavadocCommentsHaveRightPosition() throws Exception {

        assertThat(firstComment.getBeginLine(), is(3));
        assertThat(firstComment.getBeginColumn(), is(1));
        assertThat(firstComment.getEndLine(), is(3));
        assertThat(firstComment.getEndColumn(), is(32));

        assertThat(secondComment.getBeginLine(), is(10));
        assertThat(secondComment.getBeginColumn(), is(1));
        assertThat(secondComment.getEndLine(), is(10));
        assertThat(secondComment.getEndColumn(), is(34));
    }
}
