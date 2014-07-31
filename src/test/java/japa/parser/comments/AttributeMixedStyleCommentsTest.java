package japa.parser.comments;


import fixture.Helper;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.stmt.BlockStmt;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

public class AttributeMixedStyleCommentsTest {

    private CompilationUnit compilationUnit;
    private ClassOrInterfaceDeclaration classDeclaration;
    private MethodDeclaration methodDeclaration;
    private BlockStmt blockStmt;

    private static final String CLASS_WITH_MIXED_COMMENTS_FILE = "ClassWithMixedStyleComments.java";

    @Before
    public void setUp() throws Exception{
        String source = Helper.readStream(getClass().getResourceAsStream(CLASS_WITH_MIXED_COMMENTS_FILE));
        compilationUnit = Helper.parserString(source);
        classDeclaration = (ClassOrInterfaceDeclaration) compilationUnit.getChildrenNodes().get(1);
    }

    @Test
    public void testAgainNodeGetAllContainedComments() throws Exception {

        assertNotNull(compilationUnit.getComment());
        assertEquals("CompilationUnitComment", compilationUnit.getComment().getContent());

        assertEquals(2, compilationUnit.getChildrenNodes().size());
        assertNull(compilationUnit.getChildrenNodes().get(0).getComment());
        assertEquals(0, compilationUnit.getChildrenNodes().get(0).getAllContainedComments().size());
        assertNull(compilationUnit.getChildrenNodes().get(1).getComment());

        assertEquals(5, classDeclaration.getMembers().size());

        FieldDeclaration fieldA = (FieldDeclaration) classDeclaration.getMembers().get(0);
        assertNotNull(fieldA.getComment());
        assertEquals(0, fieldA.getAllContainedComments().size());

        FieldDeclaration fieldB = (FieldDeclaration) classDeclaration.getMembers().get(1);
        assertNotNull(fieldB.getComment());
        assertEquals(0, fieldB.getAllContainedComments().size());

        FieldDeclaration fieldC = (FieldDeclaration) classDeclaration.getMembers().get(2);
        assertEquals("c",fieldC.getVariables().get(0).getId().getName());
        assertNotNull(fieldC.getComment());
        assertEquals(0, fieldC.getAllContainedComments().size());

        FieldDeclaration fieldD = (FieldDeclaration) classDeclaration.getMembers().get(3);
        assertNotNull(fieldD.getComment());
        assertEquals(0, fieldD.getAllContainedComments().size());

        FieldDeclaration fieldE = (FieldDeclaration) classDeclaration.getMembers().get(4);
        assertEquals("e", fieldE.getVariables().get(0).getId().getName());
        assertNotNull(fieldE.getComment());
        assertEquals(0, fieldE.getAllContainedComments().size());

        assertEquals(6, classDeclaration.getAllContainedComments().size());
        assertEquals(6, compilationUnit.getAllContainedComments().size());

        assertEquals(0, compilationUnit.getOrphanComments().size());
    }


}
