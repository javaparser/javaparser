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

package com.github.javaparser;

import java.io.InputStream;

import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static org.junit.Assert.assertEquals;

public class TestUtils {

    public static InputStream getSampleStream(String sampleName) {
        InputStream is = TestUtils.class.getClassLoader().getResourceAsStream("com/github/javaparser/bdd/samples/"
                + sampleName + ".java");
        if (is == null) {
            throw new RuntimeException("Example not found, check your test. Sample name: " + sampleName);
        }
        return is;
    }
    
    public static void assertEqualsNoWhitespace(String expected, String actual) {
        assertEquals(stripWhitespace(expected), stripWhitespace(actual));
    }

    public static String stripWhitespace(String string) {
        return string.replaceAll("\\s","");
    }

    public static void assertInstanceOf(Class<?> expectedType, Object instance) {
        String msg = f("%s is not an instance of %s.", instance.getClass(), expectedType);
        assertEquals(msg, true, expectedType.isAssignableFrom(instance.getClass()));
    }
}
