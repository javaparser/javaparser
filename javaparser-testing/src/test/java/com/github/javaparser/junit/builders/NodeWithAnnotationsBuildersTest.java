package com.github.javaparser.junit.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class NodeWithAnnotationsBuildersTest {
    CompilationUnit cu;
    private ClassOrInterfaceDeclaration testClass;

    @Before
    public void setup() {
        cu = new CompilationUnit();
        testClass = cu.addClass("testClass");
    }

    @interface hey {

    }

    @After
    public void teardown() {
        cu = null;
        testClass = null;
    }

    @Test
    public void testAddAnnotation() {
        NormalAnnotationExpr annotation = testClass.addAnnotation(hey.class);
        assertEquals("import com.github.javaparser.junit.builders.NodeWithAnnotationsBuildersTest$hey;", cu.getImport(0).toString().trim());
        assertEquals(1, testClass.getAnnotations().size());
        assertEquals(annotation, testClass.getAnnotation(0));
        assertEquals(NormalAnnotationExpr.class, testClass.getAnnotation(0).getClass());
    }

    @Test
    public void testAddMarkerAnnotation() {
        testClass.addMarkerAnnotation("test");
        assertEquals(1, testClass.getAnnotations().size());
    }

    @Test
    public void testAddSingleMemberAnnotation() {
        testClass.addSingleMemberAnnotation("test", "value");
        assertEquals(1, testClass.getAnnotations().size());
        assertEquals("value", ((SingleMemberAnnotationExpr) testClass.getAnnotation(0)).getMemberValue().toString());
    }

    @Test
    public void testIsAnnotationPresent() {
        testClass.addMarkerAnnotation(hey.class);
        assertTrue(testClass.isAnnotationPresent(hey.class));
    }

    @Test
    public void testGetAnnotationByName() {
        NormalAnnotationExpr annotation = testClass.addAnnotation(hey.class);
        assertEquals(annotation, testClass.getAnnotationByName("hey"));
    }

    @Test
    public void testGetAnnotationByClass() {
        NormalAnnotationExpr annotation = testClass.addAnnotation(hey.class);
        assertEquals(annotation, testClass.getAnnotationByClass(hey.class));
    }
}