package com.github.javaparser;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class UnicodeEscapeProcessingProviderTest {
    @Test
    void readABadUnicodeEscape() {
        UnicodeEscapeProcessingProvider provider = new UnicodeEscapeProcessingProvider(new StringProvider("13\\u12"));
        char[] buffer = new char[10];
        assertThrows(RuntimeException.class, () -> provider.read(buffer, 0, buffer.length));
    }

    @Test
    void readSomethingWithAUnicodeEscape() {
        UnicodeEscapeProcessingProvider provider = new UnicodeEscapeProcessingProvider(new StringProvider("13\\u123498"));
        char[] buffer = new char[10];
        int read = provider.read(buffer, 0, buffer.length);

        assertEquals(5, read);
        assertEquals("13ሴ98\0\0\0\0\0", new String(buffer));
    }

    @Test
    void readFromAnEmptyProvider() {
        UnicodeEscapeProcessingProvider provider = new UnicodeEscapeProcessingProvider(new StringProvider(""));
        char[] buffer = new char[10];
        int read = provider.read(buffer, 0, buffer.length);

        assertEquals(-1, read);
        assertEquals("\0\0\0\0\0\0\0\0\0\0", new String(buffer));
    }
}

