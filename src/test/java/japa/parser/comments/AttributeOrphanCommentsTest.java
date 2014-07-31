package japa.parser.comments;

import fixture.Helper;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.stmt.BlockStmt;
import org.junit.Before;
import org.junit.Test;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.nullValue;

public class AttributeOrphanCommentsTest {

    private CompilationUnit compilationUnit;
    private ClassOrInterfaceDeclaration classDeclaration;
    private MethodDeclaration methodDeclaration;
    private BlockStmt blockStmt;

    private static final String CLASS_WITH_ORPHAN_COMMENTS_FILE = "ClassWithOrphanComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_ORPHAN_COMMENTS_FILE));
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
    public void shouldHaveSixCommentsContainedInCompilationUnit() throws Exception {

        assertThat(compilationUnit.getAllContainedComments().size(), is(6));
    }

    @Test
    public void shouldHaveOneOrphanCommentInCompilationUnit() throws Exception {

        assertThat(compilationUnit.getOrphanComments().size(), is(1));
        assertThat(compilationUnit.getOrphanComments().get(0).getContent(), is("Orphan comment inside the CompilationUnit"));
    }

    @Test
    public void shouldHaveTwoOrphanCommentInClass() throws Exception {

        assertThat(classDeclaration.getOrphanComments().size(), is(2));
        assertThat(classDeclaration.getOrphanComments().get(0).getContent(), is("a first comment floating in the class"));
        assertThat(classDeclaration.getOrphanComments().get(1).getContent(), is("a second comment floating in the class"));
    }

    @Test
    public void shouldHaveOneCommentForClassDeclaration(){

        assertThat(classDeclaration.getComment().getContent(), is("Javadoc associated with the class"));
    }

    @Test
    public void shouldHaveFourCommentsContainedInClass(){

        assertThat(classDeclaration.getAllContainedComments().size(), is(4));
    }

    @Test
    public void shouldHaveNoOrphanCommentInMethod() throws Exception {

        assertThat(methodDeclaration.getOrphanComments().size(), is(0));
    }

    @Test
    public void shouldHaveOneCommentForMethodDeclaration(){

        assertThat(methodDeclaration.getComment().getContent(), is("comment associated to the method"));
    }

    @Test
    public void shouldHaveOneCommentContainedInMethod(){
        assertThat(methodDeclaration.getAllContainedComments().get(0).getContent(), is("comment floating inside the method"));
    }

    @Test
    public void shouldHaveOneOrphanCommentInBlockStatement(){

        assertThat(blockStmt.getOrphanComments().size(), is(1));
        assertThat(blockStmt.getOrphanComments().get(0).getContent(), is("comment floating inside the method"));
    }
}
