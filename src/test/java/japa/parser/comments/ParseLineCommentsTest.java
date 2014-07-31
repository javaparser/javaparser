package japa.parser.comments;

import fixture.Helper;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.comments.CommentsCollection;
import japa.parser.ast.comments.CommentsParser;
import japa.parser.ast.comments.LineComment;

import japa.parser.ast.stmt.BlockStmt;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.is;

public class ParseLineCommentsTest {

    private CommentsCollection commentsCollection;

    private LineComment firstComment;
    private LineComment secondComment;
    private LineComment thirdComment;
    private LineComment fourthComment;

    private static final String CLASS_WITH_LINE_COMMENTS_FILE = "ClassWithLineComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_LINE_COMMENTS_FILE));
        commentsCollection = new CommentsParser().parse(source);

        firstComment = commentsCollection.getLineComments().get(0);
        secondComment = commentsCollection.getLineComments().get(1);
        thirdComment = commentsCollection.getLineComments().get(2);
        fourthComment = commentsCollection.getLineComments().get(3);
    }

    @Test
    public void shouldHaveParsedFourComments() throws Exception {

        assertThat(commentsCollection.getLineComments().size(), is(4));
    }

    @Test
    public void shouldHaveCorrectCommentContent() throws Exception {

        assertThat(firstComment.getContent(), is(" first comment"));
        assertThat(secondComment.getContent(), is(" second comment"));
        assertThat(thirdComment.getContent(), is(" third comment"));
        assertThat(fourthComment.getContent(), is(" fourth comment"));
    }

    @Test
    public void shouldHaveCorrectCommentPosition() throws Exception {

        assertThat(firstComment.getBeginLine(), is(6));
        assertThat(firstComment.getBeginColumn(), is(9));
        assertThat(firstComment.getEndLine(), is(6));
        assertThat(firstComment.getEndColumn(), is(25));

        assertThat(secondComment.getBeginLine(), is(7));
        assertThat(secondComment.getBeginColumn(), is(18));
        assertThat(secondComment.getEndLine(), is(7));
        assertThat(secondComment.getEndColumn(), is(35));

        assertThat(thirdComment.getBeginLine(), is(8));
        assertThat(thirdComment.getBeginColumn(), is(9));
        assertThat(thirdComment.getEndLine(), is(8));
        assertThat(thirdComment.getEndColumn(), is(25));

        assertThat(fourthComment.getBeginLine(), is(9));
        assertThat(fourthComment.getBeginColumn(), is(9));
        assertThat(fourthComment.getEndLine(), is(9));
        assertThat(fourthComment.getEndColumn(), is(26));
    }

}
