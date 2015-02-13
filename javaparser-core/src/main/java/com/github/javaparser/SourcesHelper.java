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
