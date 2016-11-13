package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import java.util.List;
import java.util.function.Function;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

public class ClassOrInterfaceDeclarationBuildersTest {
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
	public void testAddExtends() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        testClass.addExtends(List.class);
        assertEquals(1, cu.getImportsList().size());
        assertEquals("import " + List.class.getName() + ";" + System.getProperty("line.separator"),
                cu.getImportsList().get(0).toString());
        assertEquals(1, testClass.getExtendsList().size());
        assertEquals(List.class.getSimpleName(), testClass.getExtendsList().get(0).getName());
	}

    @Test
    public void testAddImplements() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        testClass.addImplements(Function.class);
        assertEquals(1, cu.getImportsList().size());
        assertEquals("import " + Function.class.getName() + ";" + System.getProperty("line.separator"),
                cu.getImportsList().get(0).toString());
        assertEquals(1, testClass.getImplementsList().size());
        assertEquals(Function.class.getSimpleName(), testClass.getImplementsList().get(0).getName());
    }
}
