package japa.parser.comments;

import fixture.Helper;
import japa.parser.ast.comments.CommentsCollection;
import japa.parser.ast.comments.CommentsParser;
import japa.parser.ast.comments.JavadocComment;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.is;


public class ParseOrphanCommentsTest {

    private CommentsCollection commentsCollection;

    private static final String CLASS_WITH_ORPHAN_COMMENTS_FILE = "ClassWithOrphanComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_ORPHAN_COMMENTS_FILE));
        commentsCollection = new CommentsParser().parse(source);
    }

    @Test
    public void should() throws Exception {

        assertThat(commentsCollection.size(), is(6));
    }

}
