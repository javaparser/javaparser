package com.github.javaparser.utils;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class VisitorMapTest {
    @Test
    void normalEqualsDoesDeepCompare() {
        CompilationUnit x1 = parse("class X{}");
        CompilationUnit x2 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new HashMap<>();
        map.put(x1, 1);
        map.put(x2, 2);
        assertEquals(1, map.size());
    }

    @Test
    void objectIdentityEqualsDoesShallowCompare() {
        CompilationUnit x1 = parse("class X{}");
        CompilationUnit x2 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        map.put(x2, 2);
        assertEquals(2, map.size());
    }
    
    @Test
    void visitorMapGet(){
    	CompilationUnit x1 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertEquals(1, (int)map.get(x1));
    }
    
    @Test
    void visitorMapContainsKey(){
    	CompilationUnit x1 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertTrue(map.containsKey(x1));
    }
    
    @Test
    void visitorMapPutAll(){
    	CompilationUnit x1 = parse("class X{}");
    	CompilationUnit x2 = parse("class Y{}");
    	Map<CompilationUnit, Integer> map = new HashMap<>();
    	map.put(x1, 1);
    	map.put(x2, 2);
    	Map<CompilationUnit, Integer> visitorMap = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        visitorMap.putAll(map);
        assertEquals(2, visitorMap.size());
    }
    
    @Test
    void remove(){
        CompilationUnit x1 = parse("class X{}");
        VisitorMap<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertTrue(map.containsKey(x1));
        
        map.remove(x1);
        
        assertFalse(map.containsKey(x1));
    }
}
