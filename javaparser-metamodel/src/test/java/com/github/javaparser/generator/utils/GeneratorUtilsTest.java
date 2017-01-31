package com.github.javaparser.generator.utils;

import org.junit.Test;

import static org.junit.Assert.*;

public class GeneratorUtilsTest {
    @Test
    public void setterForNormalProperty(){
        String name = GeneratorUtils.setterName("value");
        assertEquals("setValue", name);
    }

    @Test
    public void setterForBooleanProperty(){
        String name = GeneratorUtils.setterName("isBlue");
        assertEquals("setBlue", name);
    }
}
