package bdd.steps;

import japa.parser.JavaParser;
import japa.parser.ParseException;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.*;
import japa.parser.ast.comments.*;
import japa.parser.ast.expr.Expression;
import japa.parser.ast.expr.IntegerLiteralExpr;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.ExpressionStmt;
import japa.parser.ast.type.PrimitiveType;
import org.jbehave.core.annotations.*;
import org.jbehave.core.model.ExamplesTable;
import org.jbehave.core.steps.Parameters;

import java.io.ByteArrayInputStream;
import java.io.IOException;

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.nullValue;
import static org.hamcrest.text.IsEqualIgnoringWhiteSpace.equalToIgnoringWhiteSpace;
import static org.junit.Assert.assertThat;

public class CommentParsingSteps {

    private CompilationUnit compilationUnit;
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

    @When("the do not consider annotations as node start for code attribution is $value on the Java parser")
    public void whenTheDoNotConsiderAnnotationsAsNodeStartForCodeAttributionIsTrueOnTheJavaParser(boolean value) {
        JavaParser.setDoNotConsiderAnnotationsAsNodeStartForCodeAttribution(value);
    }

    @When("the class is parsed by the Java parser")
    public void whenTheClassIsParsedByTheJavaParser() throws ParseException {
        compilationUnit = JavaParser.parse(new ByteArrayInputStream(sourceUnderTest.getBytes()));
    }

    @Then("the total number of comments is $expectedCount")
    public void thenTheTotalNumberOfCommentsIs(int expectedCount) {
        assertThat(commentsCollection.size(), is(expectedCount));
    }

    @Then("line comment $position is \"$expectedContent\"")
    public void thenLineCommentIs(int position, String expectedContent) {
        LineComment lineCommentUnderTest = commentsCollection.getLineComments().get(position-1);

        assertThat(lineCommentUnderTest.getContent(), is(expectedContent));
    }

    @Then("block comment $position is \"$expectedContent\"")
    public void thenBlockCommentIs(int position, String expectedContent) {
        BlockComment lineCommentUnderTest = commentsCollection.getBlockComments().get(position - 1);

        assertThat(lineCommentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("Javadoc comment $position is \"$expectedContent\"")
    public void thenJavadocCommentIs(int position, String expectedContent) {
        JavadocComment commentUnderTest = commentsCollection.getJavadocComments().get(position- 1);

        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("the line comments have the following positions: $table")
    public void thenTheLineCommentsHaveTheFollowingPositions(ExamplesTable examplesTable) {
        int index = 0;
        for(Parameters exampleRow : examplesTable.getRowsAsParameters()){
            Comment expectedLineComment = toComment(exampleRow, new LineComment());
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
            Comment expectedLineComment = toComment(exampleRow, new BlockComment());
            Comment lineCommentUnderTest = commentsCollection.getBlockComments().get(index);

            assertThat(lineCommentUnderTest.getBeginLine(), is(expectedLineComment.getBeginLine()));
            assertThat(lineCommentUnderTest.getBeginColumn(), is(expectedLineComment.getBeginColumn()));
            assertThat(lineCommentUnderTest.getEndLine(), is(expectedLineComment.getEndLine()));
            assertThat(lineCommentUnderTest.getEndColumn(), is(expectedLineComment.getEndColumn()));
            index ++;
        }
    }

    @Then("the Javadoc comments have the following positions: $table")
    public void thenTheJavadocCommentsHaveTheFollowingPositions(ExamplesTable examplesTable) {
        int index = 0;
        for(Parameters exampleRow : examplesTable.getRowsAsParameters()){
            Comment expectedLineComment = toComment(exampleRow, new BlockComment());
            Comment lineCommentUnderTest = commentsCollection.getJavadocComments().get(index);

            assertThat(lineCommentUnderTest.getBeginLine(), is(expectedLineComment.getBeginLine()));
            assertThat(lineCommentUnderTest.getBeginColumn(), is(expectedLineComment.getBeginColumn()));
            assertThat(lineCommentUnderTest.getEndLine(), is(expectedLineComment.getEndLine()));
            assertThat(lineCommentUnderTest.getEndColumn(), is(expectedLineComment.getEndColumn()));
            index ++;
        }
    }

    @Then("the compilation unit is not commented")
    public void thenTheCompilationUnitIsNotCommented() {
        assertThat(compilationUnit.getComment(), is(nullValue()));
    }

    @Then("the compilation is commented \"$expectedContent\"")
    public void thenTheCompilationIsCommentedCompilationUnitComment(String expectedContent) {
        assertThat(compilationUnit.getComment().getContent(), is(expectedContent));
    }

    @Then("the compilation unit has $expectedCount contained comments")
    public void thenTheCompilationUnitHasContainedComments(int expectedCount) {
        assertThat(compilationUnit.getComments().size(), is(expectedCount));
    }

    @Then("the compilation unit has $expectedCount orphan comments")
    public void thenTheCompilationUnitHasExpectedCountOrphanComments(int expectedCount) {
        assertThat(compilationUnit.getOrphanComments().size(), is(expectedCount));
    }

    @Then("the compilation unit orphan comment $position is \"$expectedContent\"")
    public void thenTheCompilationUnitOrphanCommentIs(int position, String expectedContent) {
        Comment commentUnderTest = compilationUnit.getOrphanComments().get(position - 1);
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("comment $commentPosition in compilation unit is not an orphan")
    public void thenCommentInCompilationUnitIsNotAnOrphan(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.isOrphan(), is(false));
    }

    @Then("comment $commentPosition in compilation unit is an orphan")
    public void thenCommentInCompilationUnitIsAnOrphan(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.isOrphan(), is(true));
    }

    @Then("comment $commentPosition in compilation unit is \"$expectedContent\"")
    public void thenCommentInCompilationUnitIs(int position, String expectedContent) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(position - 1);
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("class $position is not commented")
    public void thenClassIsNotCommented(int position) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(position - 1);
        assertThat(classUnderTest.getComment(), is(nullValue()));
    }

    @Then("class $position is commented \"$expectedContent\"")
    public void thenClassIsCommented(int position, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(position - 1);
        assertThat(classUnderTest.getComment().getContent(), is(expectedContent));
    }

    @Then("class $position has $expectedCount total contained comments")
    public void thenClassHasTotalContainedComments(int position, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(position - 1);
        assertThat(classUnderTest.getAllContainedComments().size(), is(expectedCount));
    }

    @Then("class $position has $expectedCount orphan comment")
    @Alias("class $position has $expectedCount orphan comments")
    public void thenClassHasOrphanComments(int position, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(position - 1);
        assertThat(classUnderTest.getOrphanComments().size(), is(expectedCount));
    }

    @Then("class $classPosition orphan comment $commentPosition is \"$expectedContent\"")
    public void thenClassOrphanCommentIs(int classPosition, int commentPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        Comment commentUnderTest = classUnderTest.getOrphanComments().get(commentPosition -1 );
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("method $methodPosition in class $classPosition is commented \"$expectedContent\"")
    public void thenMethodInClassIsCommented(int methodPosition, int classPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition - 1,
                MethodDeclaration.class);
        assertThat(methodUnderTest.getComment().getContent(), equalToIgnoringWhiteSpace(expectedContent));
    }

    @Then("method $methodPosition in class $classPosition has $expectedCount total contained comments")
    public void thenMethodInClassHasTotalContainedComments(int methodPosition, int classPosition, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition - 1,
                MethodDeclaration.class);
        assertThat(methodUnderTest.getAllContainedComments().size(), is(expectedCount));
    }

    @Then("comment $commentPosition in method $methodPosition in class $classPosition is \"$expectedContent\"")
    public void thenCommentInMethodInClassIs(int commentPosition, int methodPosition, int classPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition - 1,
                MethodDeclaration.class);
        Comment commentUnderTest = methodUnderTest.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("method $methodPosition in class $classPosition has $expectedCount orphan comments")
    public void thenMethodInClassHasOrphanComments(int methodPosition, int classPosition, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition - 1,
                MethodDeclaration.class);
        assertThat(methodUnderTest.getOrphanComments().size(), is(expectedCount));
    }

    @Then("block statement in method $methodPosition in class $classPosition has $expectedCount total contained comments")
    public void thenBlockStatementInMethodInClassHasTotalContainedComments(int methodPosition, int classPosition, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition - 1,
                MethodDeclaration.class);
        BlockStmt blockStmtUnderTest = methodUnderTest.getBody();
        assertThat(blockStmtUnderTest.getAllContainedComments().size(), is(expectedCount));
    }

    @Then("block statement in method $methodPosition in class $classPosition has $expectedCount orphan comments")
    public void thenBlockStatementInMethodInClassHasOrphanComments(int methodPosition, int classPosition, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition - 1,
                MethodDeclaration.class);
        BlockStmt blockStmtUnderTest = methodUnderTest.getBody();
        assertThat(blockStmtUnderTest.getOrphanComments().size(), is(expectedCount));
    }

    @Then("block statement in method $methodPosition in class $classPosition orphan comment $commentPosition is \"$expectedContent\"")
    public void thenBlockStatementInMethodInClassIs(int methodPosition, int classPosition, int commentPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition -1,
                MethodDeclaration.class);
        BlockStmt blockStmtUnderTest = methodUnderTest.getBody();
        Comment commentUnderTest = blockStmtUnderTest.getOrphanComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("type of method $methodPosition in class $classPosition is commented \"$expectedContent\"")
    public void thenTypeOfMethodInClassIsCommented(int methodPosition, int classPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        MethodDeclaration methodUnderTest = (MethodDeclaration) getMemberByTypeAndPosition(classUnderTest, methodPosition -1,
                MethodDeclaration.class);
        Comment commentUnderTest = methodUnderTest.getType().getComment();
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("field $fieldPosition in class $classPosition contains $expectedCount comments")
    public void thenFieldInClassContainsComments(int fieldPosition, int classPosition, int expectedCount) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        assertThat(fieldUnderTest.getAllContainedComments().size(), is(expectedCount));
    }

    @Then("field $fieldPosition in class $classPosition is not commented")
    public void thenFieldInClassIsNotCommented(int fieldPosition, int classPosition) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        assertThat(fieldUnderTest.getComment(), is(nullValue()));
    }

    @Then("field $fieldPosition in class $classPosition is commented \"$expectedContent\"")
    public void thenFieldInClassIsCommented(int fieldPosition, int classPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        Comment commentUnderTest = fieldUnderTest.getComment();
        assertThat(commentUnderTest.getContent(), is(equalToIgnoringWhiteSpace(expectedContent)));
    }

    @Then("variable $variablePosition value of field $fieldPosition in class $classPosition is commented \"$expectedContent\"")
    public void thenVariableValueOfFieldInClassIsCommented(int variablePosition, int fieldPosition, int classPosition, String expectedContent) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        VariableDeclarator variableUnderTest = fieldUnderTest.getVariables().get(variablePosition - 1);
        Expression valueUnderTest = variableUnderTest.getInit();
        Comment commentUnderTest = valueUnderTest.getComment();
        assertThat(commentUnderTest.getContent(), is(expectedContent));
    }

    @Then("comment $commentPosition in compilation unit parent is ClassOrInterfaceDeclaration")
    public void thenCommentInCompilationUnitParentIsClassOrInterfaceDeclaration(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getParentNode(), instanceOf(ClassOrInterfaceDeclaration.class));
    }

    @Then("comment $commentPosition in compilation unit commented node is ClassOrInterfaceDeclaration")
    public void thenCommentInCompilationUnitCommentedNodeIsClassOrInterfaceDeclaration(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getCommentedNode(), instanceOf(ClassOrInterfaceDeclaration.class));
    }

    @Then("comment $commentPosition in compilation unit commented node is FieldDeclaration")
    public void thenCommentInCompilationUnitCommentedNodeIsFieldDeclaration(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getCommentedNode(), instanceOf(FieldDeclaration.class));
    }

    @Then("comment $commentPosition in compilation unit commented node is IntegerLiteralExpr")
    public void thenCommentInCompilationUnitCommentedNodeIsIntegerLiteralExpr(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getCommentedNode(), instanceOf(IntegerLiteralExpr.class));
    }

    @Then("comment $commentPosition in compilation unit commented node is ExpressionStmt")
    public void thenCommentInCompilationUnitCommentedNodeIsIntegerExpressionStmt(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getCommentedNode(), instanceOf(ExpressionStmt.class));
    }

    @Then("comment $commentPosition in compilation unit commented node is PrimitiveType")
    public void thenCommentInCompilationUnitCommentedNodeIsIntegerPrimitiveType(int commentPosition) {
        Comment commentUnderTest = compilationUnit.getAllContainedComments().get(commentPosition - 1);
        assertThat(commentUnderTest.getCommentedNode(), instanceOf(PrimitiveType.class));
    }

    private BodyDeclaration getMemberByTypeAndPosition(TypeDeclaration typeDeclaration, int position,
                                                       Class<? extends BodyDeclaration> typeClass){
        int typeCount = 0;
        for(BodyDeclaration declaration : typeDeclaration.getMembers()){
            if(declaration.getClass().equals(typeClass)){
                if(typeCount == position){
                    return declaration;
                }
                typeCount++;
            }
        }
        throw new IllegalArgumentException("No member " + typeClass + " at position: " + position );
    }

    private Comment toComment(Parameters row, Comment comment) {
        comment.setBeginLine(Integer.parseInt(row.values().get("beginLine")));
        comment.setBeginColumn(Integer.parseInt(row.values().get("beginColumn")));
        comment.setEndLine(Integer.parseInt(row.values().get("endLine")));
        comment.setEndColumn(Integer.parseInt(row.values().get("endColumn")));
        return comment;
    }
}
