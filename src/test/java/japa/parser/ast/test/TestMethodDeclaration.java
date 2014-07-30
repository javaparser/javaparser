package japa.parser.ast.test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.ConstructorDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * @author Federico Tomassetti
 * @since July 2014
 */
public class TestMethodDeclaration {

    @Test
    public void testGetDeclarationAsStringCompleteForm() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("AClassWithAMethod.java"));
        CompilationUnit cu = Helper.parserString(source);

        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)cu.getTypes().get(0);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(0);

        assertEquals("protected final native List<String> aMethod(int a, String b) throws This, AndThat, AndWhatElse", method.getDeclarationAsString());
    }

    @Test
    public void testGetDeclarationAsStringShortForm() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("AClassWithAMethod.java"));
        CompilationUnit cu = Helper.parserString(source);

        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)cu.getTypes().get(0);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(0);
        assertEquals("List<String> aMethod(int a, String b)", method.getDeclarationAsString(false, false));
    }
}
