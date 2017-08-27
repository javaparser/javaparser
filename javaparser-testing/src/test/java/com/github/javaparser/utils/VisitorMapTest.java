package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;
import org.junit.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class VisitorMapTest {
    @Test
    public void normalEqualsDoesDeepCompare() {
        CompilationUnit x1 = JavaParser.parse("class X{}");
        CompilationUnit x2 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> map = new HashMap<>();
        map.put(x1, 1);
        map.put(x2, 2);
        assertEquals(1, map.size());
    }

    @Test
    public void objectIdentityEqualsDoesShallowCompare() {
        CompilationUnit x1 = JavaParser.parse("class X{}");
        CompilationUnit x2 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        map.put(x2, 2);
        assertEquals(2, map.size());
    }
    
    @Test
    public void visitorMapGet(){
    	CompilationUnit x1 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertEquals(1, (int)map.get(x1));
    }
    
    @Test
    public void visitorMapContainsKey(){
    	CompilationUnit x1 = JavaParser.parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertTrue(map.containsKey(x1));
    }
    
    @Test
    public void visitorMapPutAll(){
    	CompilationUnit x1 = JavaParser.parse("class X{}");
    	CompilationUnit x2 = JavaParser.parse("class Y{}");
    	Map<CompilationUnit, Integer> map = new HashMap<>();
    	map.put(x1, 1);
    	map.put(x2, 2);
    	Map<CompilationUnit, Integer> visitorMap = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        visitorMap.putAll(map);
        assertEquals(2, visitorMap.size());
    }
    
    @Test
    public void remove(){
        CompilationUnit x1 = JavaParser.parse("class X{}");
        VisitorMap<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertTrue(map.containsKey(x1));
        
        map.remove(x1);
        
        assertFalse(map.containsKey(x1));
    }
}
