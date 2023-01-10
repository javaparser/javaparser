package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.utils.TypeUtils;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TypeDescriptorTest {
    @Test
    public void primitiveTypeDescriptorTest() {
        assertEquals("V", TypeUtils.getPrimitiveTypeDescriptor(void.class));
        assertEquals("V", TypeUtils.getPrimitiveTypeDescriptor(Void.class));

        assertEquals("Z", TypeUtils.getPrimitiveTypeDescriptor(boolean.class));
        assertEquals("Z", TypeUtils.getPrimitiveTypeDescriptor(Boolean.class));

        assertEquals("C", TypeUtils.getPrimitiveTypeDescriptor(char.class));
        assertEquals("C", TypeUtils.getPrimitiveTypeDescriptor(Character.class));

        assertEquals("B", TypeUtils.getPrimitiveTypeDescriptor(byte.class));
        assertEquals("B", TypeUtils.getPrimitiveTypeDescriptor(Byte.class));

        assertEquals("S", TypeUtils.getPrimitiveTypeDescriptor(short.class));
        assertEquals("S", TypeUtils.getPrimitiveTypeDescriptor(Short.class));

        assertEquals("I", TypeUtils.getPrimitiveTypeDescriptor(int.class));
        assertEquals("I", TypeUtils.getPrimitiveTypeDescriptor(Integer.class));

        assertEquals("J", TypeUtils.getPrimitiveTypeDescriptor(long.class));
        assertEquals("J", TypeUtils.getPrimitiveTypeDescriptor(Long.class));

        assertEquals("F", TypeUtils.getPrimitiveTypeDescriptor(float.class));
        assertEquals("F", TypeUtils.getPrimitiveTypeDescriptor(Float.class));

        assertEquals("D", TypeUtils.getPrimitiveTypeDescriptor(double.class));
        assertEquals("D", TypeUtils.getPrimitiveTypeDescriptor(Double.class));
    }
}
