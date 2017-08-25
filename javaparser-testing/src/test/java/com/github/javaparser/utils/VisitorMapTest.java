package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;
import org.junit.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class VisitorMapTest {
    @Test
    public void normalEqualsDoesDeepCompare() {
        CompilationUnit x1 = JavaParser.parse("class X{}");
        CompilationUnit x2 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> normalMap = new HashMap<>();
        normalMap.put(x1, 1);
        normalMap.put(x2, 2);
        assertEquals(1, normalMap.size());
    }

    @Test
    public void objectIdentityEqualsDoesShallowCompare() {
        CompilationUnit x1 = JavaParser.parse("class X{}");
        CompilationUnit x2 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> normalMap = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        normalMap.put(x1, 1);
        normalMap.put(x2, 2);
        assertEquals(2, normalMap.size());
    }
    
    @Test
    public void visitorMapGet(){
    	CompilationUnit x1 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> normalMap = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        normalMap.put(x1, 1);
        assertEquals(1, (int)normalMap.get(x1));
    }
    
    @Test
    public void visitorMapContainsKey(){
    	CompilationUnit x1 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> normalMap = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        normalMap.put(x1, 1);
        assertTrue(normalMap.containsKey(x1));
    }
    
    @Test
    public void visitorMapPutAll(){
    	CompilationUnit x1 = JavaParser.parse("class X{}");
    	CompilationUnit x2 = JavaParser.parse("class Y{}");
    	Map<CompilationUnit, Integer> normalMap = new HashMap<>();
    	normalMap.put(x1, 1);
    	normalMap.put(x2, 2);
    	Map<CompilationUnit, Integer> visitorMap = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        visitorMap.putAll(normalMap);
        assertEquals(2, visitorMap.size());
    }
    

}