package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import java.util.function.Function;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.EnumDeclaration;

public class EnumDeclarationBuildersTest {
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
    public void testAddImplements() {
        EnumDeclaration testEnum = cu.addEnum("test");
        testEnum.addImplements(Function.class);
        assertEquals(1, cu.getImportsList().size());
        assertEquals("import " + Function.class.getName() + ";" + System.getProperty("line.separator"),
                cu.getImportsList().get(0).toString());
        assertEquals(1, testEnum.getImplementsList().size());
        assertEquals(Function.class.getSimpleName(), testEnum.getImplementsList().get(0).getName());
    }

    @Test
    public void testAddEnumConstant() {
        EnumDeclaration testEnum = cu.addEnum("test");
        testEnum.addEnumConstant("MY_ENUM_CONSTANT");
        assertEquals(1, testEnum.getEntriesList().size());
        assertEquals("MY_ENUM_CONSTANT", testEnum.getEntriesList().get(0).getName());
    }
}
