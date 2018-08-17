package com.github.javaparser.utils;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;
import org.junit.Test;

import java.util.HashMap;
import java.util.Map;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.Assert.*;

public class VisitorMapTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void normalEqualsDoesDeepCompare() {
        CompilationUnit x1 = parse("class X{}");
        CompilationUnit x2 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new HashMap<>();
        map.put(x1, 1);
        map.put(x2, 2);
        assertEquals(1, map.size());
    }

    @Test
    public void objectIdentityEqualsDoesShallowCompare() {
        CompilationUnit x1 = parse("class X{}");
        CompilationUnit x2 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        map.put(x2, 2);
        assertEquals(2, map.size());
    }

    @Test
    public void visitorMapGet() {
        CompilationUnit x1 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertEquals(1, (int) map.get(x1));
    }

    @Test
    public void visitorMapContainsKey() {
        CompilationUnit x1 = parse("class X{}");

        Map<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertTrue(map.containsKey(x1));
    }

    @Test
    public void visitorMapPutAll() {
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
    public void remove() {
        CompilationUnit x1 = parse("class X{}");
        VisitorMap<CompilationUnit, Integer> map = new VisitorMap<>(new ObjectIdentityHashCodeVisitor(), new ObjectIdentityEqualsVisitor());
        map.put(x1, 1);
        assertTrue(map.containsKey(x1));

        map.remove(x1);

        assertFalse(map.containsKey(x1));
    }
}
