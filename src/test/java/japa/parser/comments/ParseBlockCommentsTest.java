package japa.parser.comments;

import fixture.Helper;
import japa.parser.ast.comments.BlockComment;
import japa.parser.ast.comments.CommentsCollection;
import japa.parser.ast.comments.CommentsParser;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.is;

public class ParseBlockCommentsTest {

    private CommentsCollection commentsCollection;
    private BlockComment firstComment;
    private BlockComment secondComment;
    private BlockComment thirdComment;
    private BlockComment fourthComment;
    private BlockComment fifthComment;

    private static final String CLASS_WITH_BLOCK_COMMENTS_FILE = "ClassWithBlockComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_BLOCK_COMMENTS_FILE));
        commentsCollection = new CommentsParser().parse(source);

        firstComment = commentsCollection.getBlockComments().get(0);
        secondComment = commentsCollection.getBlockComments().get(1);
        thirdComment = commentsCollection.getBlockComments().get(2);
        fourthComment = commentsCollection.getBlockComments().get(3);
        fifthComment = commentsCollection.getBlockComments().get(4);
    }

    @Test
    public void shouldHaveParsedFiveComments() throws Exception {

        assertThat(commentsCollection.size(), is(5));
    }

    @Test
    public void testBlockCommentsHaveRightContent() throws Exception {

        assertThat(firstComment.getContent(), is(" comment which is not attributed to the class, it floats around as an orphan "));
        assertThat(secondComment.getContent(), is(" comment to a class "));
        assertThat(thirdComment.getContent(), is(" comment to a method "));
        assertThat(fourthComment.getContent(), is(" comment put randomly in class:\n" +
                                                    "\n" +
                                                    "    another orphan.\n" +
                                                    "    It spans over more lines "));
        assertThat(fifthComment.getContent(), is(" a comment lost inside a compilation unit. It is orphan, I am sure you got this one "));
    }

    @Test
    public void testBlockCommentsHaveRightPosition() throws Exception {

        assertThat(firstComment.getBeginLine(), is(3));
        assertThat(firstComment.getBeginColumn(), is(1));
        assertThat(firstComment.getEndLine(), is(3));
        assertThat(firstComment.getEndColumn(), is(82));

        assertThat(secondComment.getBeginLine(), is(4));
        assertThat(secondComment.getBeginColumn(), is(1));
        assertThat(secondComment.getEndLine(), is(4));
        assertThat(secondComment.getEndColumn(), is(25));

        assertThat(thirdComment.getBeginLine(), is(7));
        assertThat(thirdComment.getBeginColumn(), is(5));
        assertThat(thirdComment.getEndLine(), is(7));
        assertThat(thirdComment.getEndColumn(), is(30));

        assertThat(fourthComment.getBeginLine(), is(10));
        assertThat(fourthComment.getBeginColumn(), is(5));
        assertThat(fourthComment.getEndLine(), is(13));
        assertThat(fourthComment.getEndColumn(), is(32));

        assertThat(fifthComment.getBeginLine(), is(17));
        assertThat(fifthComment.getBeginColumn(), is(1));
        assertThat(fifthComment.getEndLine(), is(17));
        assertThat(fifthComment.getEndColumn(), is(89));
    }
}
