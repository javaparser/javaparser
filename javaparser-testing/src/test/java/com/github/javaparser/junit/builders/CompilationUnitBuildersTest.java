package com.github.javaparser.junit.builders;

import static com.github.javaparser.utils.Utils.EOL;
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
		assertEquals("import " + Map.class.getName() + ";" + EOL, cu.getImport(0).toString());
		assertEquals("import " + List.class.getName() + ";" + EOL, cu.getImport(1).toString());
		assertEquals("import myImport;" + EOL, cu.getImport(2).toString());
	}

    @Test
    public void testAddClass() {
        ClassOrInterfaceDeclaration myClassDeclaration = cu.addClass("testClass", Modifier.PRIVATE);
        assertEquals(1, cu.getTypes().size());
        assertEquals("testClass", cu.getType(0).getNameAsString());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
        assertTrue(myClassDeclaration.isPrivate());
        assertFalse(myClassDeclaration.isInterface());
    }

    @Test
    public void testAddInterface() {
        ClassOrInterfaceDeclaration myInterfaceDeclaration = cu.addInterface("testInterface");
        assertEquals(1, cu.getTypes().size());
        assertEquals("testInterface", cu.getType(0).getNameAsString());
        assertTrue(myInterfaceDeclaration.isPublic());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
        assertTrue(myInterfaceDeclaration.isInterface());
    }

    @Test
    public void testAddEnum() {
        EnumDeclaration myEnumDeclaration = cu.addEnum("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getType(0).getNameAsString());
        assertTrue(myEnumDeclaration.isPublic());
        assertEquals(EnumDeclaration.class, cu.getType(0).getClass());
    }

    @Test
    public void testAddAnnotationDeclaration() {
        AnnotationDeclaration myAnnotationDeclaration = cu.addAnnotationDeclaration("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getType(0).getNameAsString());
        assertTrue(myAnnotationDeclaration.isPublic());
        assertEquals(AnnotationDeclaration.class, cu.getType(0).getClass());
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
