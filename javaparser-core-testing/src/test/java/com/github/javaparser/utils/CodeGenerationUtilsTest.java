package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.CodeGenerationUtils.*;
import static org.junit.jupiter.api.Assertions.*;

class CodeGenerationUtilsTest {
    @Test
    void setters() {
        assertEquals("setValue", setterName("value"));
        assertEquals("setBlue", setterName("isBlue"));
    }

    @Test
    void getters() {
        assertEquals("getValue", getterName(Object.class, "value"));
        assertEquals("isBlue", getterName(Boolean.class, "isBlue"));
        assertEquals("isBlue", getterName(Boolean.class, "blue"));
    }

}
