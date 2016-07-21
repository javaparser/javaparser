package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Map;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;

public class CompilationUnitBuildersTest {
	CompilationUnit cu;

	@Before
	public void setup() {
		cu = new CompilationUnit();
	}

	@After
	public void teardown() {
		cu = null;
	}

	@Test
	public void testAddImport() {
		cu.addImport(Map.class);
		cu.addImport(Map.class);
		cu.addImport(List.class);
		assertEquals(2, cu.getImports().size());
		cu.addImport("myImport");
		assertEquals(3, cu.getImports().size());
		assertEquals("import " + Map.class.getName() + ";" + System.getProperty("line.separator"), cu.getImports().get(0).toString());
		assertEquals("import " + List.class.getName() + ";" + System.getProperty("line.separator"), cu.getImports().get(1).toString());
		assertEquals("import myImport;" + System.getProperty("line.separator"), cu.getImports().get(2).toString());
	}

    @Test
    public void testAddClass() {
        ClassOrInterfaceDeclaration myClassDeclaration = cu.addClass("testClass", Modifier.PRIVATE.toEnumSet());
        assertEquals(1, cu.getTypes().size());
        assertEquals("testClass", cu.getTypes().get(0).getName());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getTypes().get(0).getClass());
        assertTrue(myClassDeclaration.getModifiers().equals(Modifier.PRIVATE.toEnumSet()));
        assertFalse(myClassDeclaration.isInterface());
    }

    @Test
    public void testAddInterface() {
        ClassOrInterfaceDeclaration myInterfaceDeclaration = cu.addInterface("testInterface");
        assertEquals(1, cu.getTypes().size());
        assertEquals("testInterface", cu.getTypes().get(0).getName());
        assertTrue(myInterfaceDeclaration.getModifiers().equals(Modifier.PUBLIC.toEnumSet()));
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getTypes().get(0).getClass());
        assertTrue(myInterfaceDeclaration.isInterface());
    }

    @Test
    public void testAddEnum() {
        EnumDeclaration myEnumDeclaration = cu.addEnum("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getTypes().get(0).getName());
        assertTrue(myEnumDeclaration.getModifiers().equals(Modifier.PUBLIC.toEnumSet()));
        assertEquals(EnumDeclaration.class, cu.getTypes().get(0).getClass());
    }

    @Test
    public void testAddAnnotationDeclaration() {
        AnnotationDeclaration myAnnotationDeclaration = cu.addAnnotationDeclaration("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getTypes().get(0).getName());
        assertTrue(myAnnotationDeclaration.getModifiers().equals(Modifier.PUBLIC.toEnumSet()));
        assertEquals(AnnotationDeclaration.class, cu.getTypes().get(0).getClass());
    }

    @Test
    public void testGetClassByName() {
        assertEquals(cu.addClass("test"), cu.getClassByName("test"));
    }

    @Test
    public void testGetInterfaceByName() {
        assertEquals(cu.addInterface("test"), cu.getInterfaceByName("test"));
    }

    @Test
    public void testGetEnumByName() {
        assertEquals(cu.addEnum("test"), cu.getEnumByName("test"));
    }

    @Test
    public void testGetAnnotationDeclarationByName() {
        assertEquals(cu.addAnnotationDeclaration("test"), cu.getAnnotationDeclarationByName("test"));
    }
}
