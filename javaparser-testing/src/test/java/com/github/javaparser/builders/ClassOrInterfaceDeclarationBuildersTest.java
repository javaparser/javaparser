package com.github.javaparser.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.List;
import java.util.function.Function;

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

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
                cu.getImport(0).toString());
        assertEquals(1, testClass.getExtendedTypes().size());
        assertEquals(List.class.getSimpleName(), testClass.getExtendedTypes(0).getNameAsString());
    }

    @Test
    public void testAddImplements() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        testClass.addImplements(Function.class);
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + Function.class.getName() + ";" + EOL,
                cu.getImport(0).toString());
        assertEquals(1, testClass.getImplementedTypes().size());
        assertEquals(Function.class.getSimpleName(), testClass.getImplementedTypes(0).getNameAsString());
    }
}
