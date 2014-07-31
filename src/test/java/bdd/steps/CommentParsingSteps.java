package bdd.steps;

import japa.parser.ast.comments.*;
import org.jbehave.core.annotations.*;
import org.jbehave.core.model.ExamplesTable;
import org.jbehave.core.steps.Parameters;

import java.io.IOException;
import java.util.Map;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.text.IsEqualIgnoringWhiteSpace.equalToIgnoringWhiteSpace;
import static org.junit.Assert.assertThat;

public class CommentParsingSteps {

    private CommentsCollection commentsCollection;
    private String sourceUnderTest;


    @Given("the class:$classSrc")
    public void givenTheClass(String classSrc) {
        this.sourceUnderTest = classSrc.trim();
    }

    @When("the class is parsed by the comment parser")
    public void whenTheClassIsParsedByTheCommentParser() throws IOException {
        commentsCollection = new CommentsParser().parse(sourceUnderTest);
    }

    @Then("the total number of line comments is $expectedCount")
    public void thenTheTotalNumberOfLineCommentsIsCount(int $expectedCount) {
        assertThat(commentsCollection.size(), is($expectedCount));
    }

    @Then("line comment $position is \"$expectedContent\"")
    public void thenLineCommentAtPositionHasExpectedContent(int position, String expectedContent) {
        LineComment lineCommentUnderTest = commentsCollection.getLineComments().get(position-1);

        assertThat(lineCommentUnderTest.getContent(), is(expectedContent));
    }

    @Then("block comment $position is \"$expectedContent\"")
    public void thenBlockCommentAtPositionHasExpectedContent(int position, String expectedContent) {
        BlockComment lineCommentUnderTest = commentsCollection.getBlockComments().get(position - 1);

        assertThat(lineCommentUnderTest.getContent(), equalToIgnoringWhiteSpace(expectedContent));
    }

    @Then("the line comments have the following positions: $table")
    public void thenTheLineCommentsHaveTheFollowingPositions(ExamplesTable examplesTable) {
        int index = 0;
        for(Parameters exampleRow : examplesTable.getRowsAsParameters()){
            Comment expectedLineComment = toLineComment(exampleRow, new LineComment());
            Comment lineCommentUnderTest = commentsCollection.getLineComments().get(index);

            assertThat(lineCommentUnderTest.getBeginLine(), is(expectedLineComment.getBeginLine()));
            assertThat(lineCommentUnderTest.getBeginColumn(), is(expectedLineComment.getBeginColumn()));
            assertThat(lineCommentUnderTest.getEndLine(), is(expectedLineComment.getEndLine()));
            assertThat(lineCommentUnderTest.getEndColumn(), is(expectedLineComment.getEndColumn()));
            index ++;
        }
    }

    @Then("the block comments have the following positions: $table")
    public void thenTheBlockCommentsHaveTheFollowingPositions(ExamplesTable examplesTable) {
        int index = 0;
        for(Parameters exampleRow : examplesTable.getRowsAsParameters()){
            Comment expectedLineComment = toLineComment(exampleRow, new BlockComment());
            Comment lineCommentUnderTest = commentsCollection.getBlockComments().get(index);

            assertThat(lineCommentUnderTest.getBeginLine(), is(expectedLineComment.getBeginLine()));
            assertThat(lineCommentUnderTest.getBeginColumn(), is(expectedLineComment.getBeginColumn()));
            assertThat(lineCommentUnderTest.getEndLine(), is(expectedLineComment.getEndLine()));
            assertThat(lineCommentUnderTest.getEndColumn(), is(expectedLineComment.getEndColumn()));
            index ++;
        }
    }

    private Comment toLineComment(Parameters row, Comment comment) {
        comment.setBeginLine(Integer.parseInt(row.values().get("beginLine")));
        comment.setBeginColumn(Integer.parseInt(row.values().get("beginColumn")));
        comment.setEndLine(Integer.parseInt(row.values().get("endLine")));
        comment.setEndColumn(Integer.parseInt(row.values().get("endColumn")));
        return comment;
    }

}
