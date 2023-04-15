/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.utils;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

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
