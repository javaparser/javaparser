package japa.parser.ast;

import fixture.Helper;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.type.ReferenceType;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public class TestAnnotationParsing {

    /**
     * See Issue 37.
     * @throws Exception
     */
    @Test
    public void testParsingStringLiteralsContainingColon() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("Issue37.java"));
        CompilationUnit cu = Helper.parserString(source);
        TypeDeclaration classDecl = cu.getTypes().get(0);
        FieldDeclaration fieldDecl = (FieldDeclaration)classDecl.getMembers().get(1);
        AnnotationExpr annotation = fieldDecl.getAnnotations().get(0);
        ReferenceType fieldType = (ReferenceType)fieldDecl.getType();
        assertNull(fieldType.getComment());
    }

}
