package japa.parser.ast.test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.ConstructorDeclaration;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

/**
 * @author Federico Tomassetti
 * @since July 2014
 */
public class TestConstructorDeclaration {

    @Test
    public void testGetDeclarationAsStringCompleteForm() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("AClassWithAConstructor.java"));
        CompilationUnit cu = Helper.parserString(source);

        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)cu.getTypes().get(0);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(0);
        assertEquals("protected ClassWithAConstructor(int a, String b) throws This, AndThat, AndWhatElse", constructor.getDeclarationAsString());
    }

    @Test
    public void testGetDeclarationAsStringShortForm() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("AClassWithAConstructor.java"));
        CompilationUnit cu = Helper.parserString(source);

        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)cu.getTypes().get(0);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(0);
        assertEquals("ClassWithAConstructor(int a, String b)", constructor.getDeclarationAsString(false, false));
    }
}
