package japa.parser.comments;

import fixture.Helper;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.stmt.BlockStmt;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.nullValue;

public class AttributeLineCommentsTest {

    private CompilationUnit compilationUnit;
    private ClassOrInterfaceDeclaration classDeclaration;
    private MethodDeclaration methodDeclaration;
    private BlockStmt blockStmt;

    private static final String CLASS_WITH_LINE_COMMENTS_FILE = "ClassWithLineComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_LINE_COMMENTS_FILE));
        compilationUnit = Helper.parserString(source);
        classDeclaration = (ClassOrInterfaceDeclaration) compilationUnit.getChildrenNodes().get(1);
        methodDeclaration = (MethodDeclaration) classDeclaration.getMembers().get(0);
        blockStmt = methodDeclaration.getBody();
    }

    @Test
    public void shouldHaveNoCommentAssignedToCompilationUnit() throws Exception {

        assertThat(compilationUnit.getComment(), nullValue());
    }

    @Test
    public void shouldHaveNoOrphanCommentInCompilationUnit() throws Exception {

        assertThat(compilationUnit.getOrphanComments().size(), is(0));
    }

    @Test
    public void shouldHaveFourCommentsContainedInCompilationUnit() throws Exception {

        assertThat(compilationUnit.getAllContainedComments().size(), is(4));
    }

    @Test
    public void shouldHaveFourCommentsContainedInClass() throws Exception {

        assertThat(classDeclaration.getAllContainedComments().size(), is(4));
    }

    @Test
    public void shouldHaveFourCommentsContainedInMethod() throws Exception {

        assertThat(methodDeclaration.getAllContainedComments().size(), is(4));
    }

    @Test
    public void shouldHaveNoOrphanCommentsContainedInMethod() throws Exception {

        assertThat(methodDeclaration.getOrphanComments().size(), is(0));
    }

    @Test
    public void shouldHaveFourCommentsContainedInBlockStatement() throws Exception {

        assertThat(blockStmt.getAllContainedComments().size(), is(4));
    }

    @Test
    public void shouldHaveThreeOrphanCommentsContainedInBlockStatement() throws Exception {

        assertThat(blockStmt.getOrphanComments().size(), is(3));
    }

}

