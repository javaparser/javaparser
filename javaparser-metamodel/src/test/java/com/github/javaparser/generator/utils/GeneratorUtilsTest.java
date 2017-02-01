package com.github.javaparser.generator.utils;

import org.junit.Test;

import static com.github.javaparser.generator.utils.GeneratorUtils.*;
import static org.junit.Assert.*;

public class GeneratorUtilsTest {
    @Test
    public void setters() {
        assertEquals("setValue", setterName("value"));
        assertEquals("setBlue", setterName("isBlue"));
    }

    @Test
    public void getters() {
        assertEquals("getValue", getterName(Object.class, "value"));
        assertEquals("isBlue", getterName(Boolean.class, "isBlue"));
        assertEquals("isBlue", getterName(Boolean.class, "blue"));
    }

    @Test
    public void screamingEmptyString() {
        assertEquals("", camelCaseToScreaming(""));
        assertEquals("ABC", camelCaseToScreaming("abc"));
        assertEquals("HELLO_HELLO", camelCaseToScreaming("HelloHello"));
        assertEquals("APE_TAIL", camelCaseToScreaming("apeTail"));
    }
}
