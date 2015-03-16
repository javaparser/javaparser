/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.utils;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * @author Didier Villevalois
 */
public class TestResources {

    private final String testResourcesPath;
    private final String directory;

    public TestResources(String testResourcesPath, String directory) {
        this.testResourcesPath = testResourcesPath;
        this.directory = directory;
    }

    public String getResourceAsString(String path) throws IOException {
        return getResourceAsString(path, "UTF-8");
    }

    public String getResourceAsString(String path, String encoding) throws IOException {
        path = path.startsWith("/") ? path : '/' + path;
        return fromStream(getResourceAsStream(path), encoding);
    }

    public InputStream getResourceAsStream(String path) {
        String fullPath = testResourcesPath + directory + path;
        InputStream inputStream = ClassLoader.getSystemResourceAsStream(fullPath);
        if (inputStream == null)
            throw new IllegalArgumentException("No such resource " + fullPath);
        return inputStream;
    }

    private String fromStream(InputStream inputStream, String encoding)
            throws IOException {
        return new String(readFully(inputStream), encoding);
    }

    private byte[] readFully(InputStream inputStream)
            throws IOException {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        byte[] buffer = new byte[1024];
        int length = 0;
        while ((length = inputStream.read(buffer)) != -1) {
            baos.write(buffer, 0, length);
        }
        return baos.toByteArray();
    }
}
