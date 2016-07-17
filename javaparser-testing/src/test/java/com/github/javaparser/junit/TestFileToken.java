package com.github.javaparser.junit;

import org.apache.commons.io.IOUtils;

import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * Creates a temporary test file that a sample can use. This way we don't have to rewrite the samples to fit them into
 * these tests.
 */
public class TestFileToken implements AutoCloseable {
    private final String filename;

    public TestFileToken(String filename) {
        this.filename = filename;
        try {
            try (InputStream i = getClass().getResourceAsStream("TestFile.java"); OutputStream o = new FileOutputStream(filename)) {
                assertNotNull(i);
                IOUtils.copy(i, o);
            }
        } catch (Exception e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

    @Override
    public void close() {
        boolean deleted = new File(filename).delete();
        assertTrue(deleted);
    }
}
