package japa.parser.comments;


import fixture.Helper;
import japa.parser.ast.comments.*;
import org.junit.Before;
import org.junit.Test;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;

public class ParseMixedStyleCommentsTest {
    private CommentsCollection commentsCollection;

    private static final String CLASS_WITH_MIXED_COMMENTS_FILE = "ClassWithMixedStyleComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_MIXED_COMMENTS_FILE));
        commentsCollection = new CommentsParser().parse(source);
    }

    @Test
    public void shouldHaveParsedSixCommentsInTotal() throws Exception {

        assertThat(commentsCollection.size(), is(7));
    }

    @Test
    public void shouldHaveCorrectLineCommentPosition() throws Exception {
        LineComment firstComment = commentsCollection.getLineComments().get(0);
        LineComment secondComment = commentsCollection.getLineComments().get(1);
        LineComment thirdComment = commentsCollection.getLineComments().get(2);
        LineComment fourthComment = commentsCollection.getLineComments().get(3);

        assertThat(firstComment.getBeginLine(), is(5));
        assertThat(firstComment.getBeginColumn(), is(5));
        assertThat(firstComment.getEndLine(), is(5));
        assertThat(firstComment.getEndColumn(), is(20));

        assertThat(secondComment.getBeginLine(), is(7));
        assertThat(secondComment.getBeginColumn(), is(5));
        assertThat(secondComment.getEndLine(), is(7));
        assertThat(secondComment.getEndColumn(), is(28));

        assertThat(thirdComment.getBeginLine(), is(9));
        assertThat(thirdComment.getBeginColumn(), is(5));
        assertThat(thirdComment.getEndLine(), is(9));
        assertThat(thirdComment.getEndColumn(), is(20));

        assertThat(fourthComment.getBeginLine(), is(19));
        assertThat(fourthComment.getBeginColumn(), is(5));
        assertThat(fourthComment.getEndLine(), is(19));
        assertThat(fourthComment.getEndColumn(), is(21));
    }

    @Test
    public void shouldHaveCorrectBlockCommentPosition() throws Exception {
        BlockComment firstComment = commentsCollection.getBlockComments().get(0);
        BlockComment secondComment = commentsCollection.getBlockComments().get(1);

        assertThat(firstComment.getBeginLine(), is(1));
        assertThat(firstComment.getBeginColumn(), is(1));
        assertThat(firstComment.getEndLine(), is(1));
        assertThat(firstComment.getEndColumn(), is(27));

        assertThat(secondComment.getBeginLine(), is(11));
        assertThat(secondComment.getBeginColumn(), is(5));
        assertThat(secondComment.getEndLine(), is(13));
        assertThat(secondComment.getEndColumn(), is(7));
    }

    @Test
    public void shouldHaveCorrectJavadocCommentPosition() throws Exception {
        JavadocComment firstComment = commentsCollection.getJavadocComments().get(0);

        assertThat(firstComment.getBeginLine(), is(15));
        assertThat(firstComment.getBeginColumn(), is(5));
        assertThat(firstComment.getEndLine(), is(17));
        assertThat(firstComment.getEndColumn(), is(8));
    }
}
