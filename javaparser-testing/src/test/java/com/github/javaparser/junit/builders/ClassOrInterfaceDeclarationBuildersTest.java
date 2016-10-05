package com.github.javaparser.junit.builders;

import static com.github.javaparser.utils.Utils.*;
import static org.junit.Assert.assertEquals;

import java.util.List;
import java.util.function.Function;

import com.github.javaparser.utils.Utils;
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
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + List.class.getName() + ";" + EOL,
                cu.getImports().get(0).toString());
        assertEquals(1, testClass.getExtends().size());
        assertEquals(List.class.getSimpleName(), testClass.getExtends().get(0).getName());
	}

    @Test
    public void testAddImplements() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        testClass.addImplements(Function.class);
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + Function.class.getName() + ";" + EOL,
                cu.getImports().get(0).toString());
        assertEquals(1, testClass.getImplements().size());
        assertEquals(Function.class.getSimpleName(), testClass.getImplements().get(0).getName());
    }
}