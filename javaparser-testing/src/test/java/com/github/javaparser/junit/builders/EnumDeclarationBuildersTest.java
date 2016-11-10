package com.github.javaparser.junit.builders;

import static com.github.javaparser.utils.Utils.EOL;
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
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + Function.class.getName() + ";" + EOL,
                cu.getImports().get(0).toString());
        assertEquals(1, testEnum.getImplements().size());
        assertEquals(Function.class.getSimpleName(), testEnum.getImplements().get(0).getNameAsString());
    }

    @Test
    public void testAddEnumConstant() {
        EnumDeclaration testEnum = cu.addEnum("test");
        testEnum.addEnumConstant("MY_ENUM_CONSTANT");
        assertEquals(1, testEnum.getEntries().size());
        assertEquals("MY_ENUM_CONSTANT", testEnum.getEntries().get(0).getNameAsString());
    }
}