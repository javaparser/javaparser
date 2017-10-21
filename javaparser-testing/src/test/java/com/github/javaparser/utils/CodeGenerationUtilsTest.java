package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.CodeGenerationUtils.*;
import static org.junit.jupiter.api.Assertions.*;

public class CodeGenerationUtilsTest {
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

}
