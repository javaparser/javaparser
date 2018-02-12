/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import java.io.*;

public class SourcesHelper {

    static String streamToString(InputStream in, String encoding){
        if (encoding == null) {
            return streamToString(in);
        } else {
            java.util.Scanner s = new java.util.Scanner(in, encoding).useDelimiter("\\A");
            return s.hasNext() ? s.next() : "";
        }
    }

    static String streamToString(InputStream in){
        java.util.Scanner s = new java.util.Scanner(in).useDelimiter("\\A");
        return s.hasNext() ? s.next() : "";
    }

    static InputStream stringToStream(String s, String encoding) throws UnsupportedEncodingException {
        byte[] rawData = encoding != null ? s.getBytes(encoding) : s.getBytes();
        return new ByteArrayInputStream(rawData);
    }

    static String readerToString(Reader reader) throws IOException {
        char[] arr = new char[8*1024]; // 8K at a time
        StringBuilder buf = new StringBuilder();
        int numChars;

        while ((numChars = reader.read(arr, 0, arr.length)) > 0) {
            buf.append(arr, 0, numChars);
        }

        return buf.toString();
    }

    static Reader stringToReader(String s){
        return new StringReader(s);
    }

}
