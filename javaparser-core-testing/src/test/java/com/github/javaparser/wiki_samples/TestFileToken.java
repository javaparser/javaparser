/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.wiki_samples;

import org.apache.commons.io.IOUtils;

import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStream;

import static org.junit.Assert.*;

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
