/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.utils.CodeGenerationUtils;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

public abstract class AbstractSymbolResolutionTest {

    protected enum TestJdk {
        JDK8(8),
        JDK9(9),
        JDK10(10),
        JDK11(11),
        JDK12(12),
        JDK13(13),
        JDK14(14),
        JDK15(15),
        UNKNOWN(null);

        private final Integer major;

        TestJdk(Integer major) {
            this.major = major;
        }

        public int getMajorVersion() {
            return this.major;
        }

        public static TestJdk getCurrentHostJdk() {
            String javaVersion = System.getProperty("java.version");

            // JavaParser explicitly requires a minimum of JDK8 to build.
            if(javaVersion.equals("8") || javaVersion.startsWith("1.8") || javaVersion.startsWith("8")) {
                return JDK8;
            } else if(javaVersion.equals("9") || javaVersion.startsWith("9.")) {
                return JDK9;
            } else if(javaVersion.equals("10") || javaVersion.startsWith("10.")) {
                return JDK10;
            } else if(javaVersion.equals("11") || javaVersion.startsWith("11.")) {
                return JDK11;
            } else if(javaVersion.equals("12") || javaVersion.startsWith("12.")) {
                return JDK12;
            } else if(javaVersion.equals("13") || javaVersion.startsWith("13.")) {
                return JDK13;
            } else if(javaVersion.equals("14") || javaVersion.startsWith("14.")) {
                return JDK14;
            } else if(javaVersion.equals("15") || javaVersion.startsWith("15.")) {
                return JDK15;
            }

            return UNKNOWN;
        }

        @Override
        public String toString() {
            return "TestJdk{" +
                    "System.getProperty(\"java.version\")=" + System.getProperty("java.version") +
                    ",major=" + major +
                    '}';
        }
    }

    protected static Path adaptPath(Path path) {
        if (Files.exists(path)) {
            return path.toAbsolutePath();
        }
        Path underSymbolSolver = CodeGenerationUtils.mavenModuleRoot(AbstractSymbolResolutionTest.class).resolve("javaparser-symbol-solver-testing").resolve(path);
        if (Files.exists(underSymbolSolver)) {
            return underSymbolSolver;
        } else {
            throw new IllegalArgumentException("I cannot adapt the path " + path);
        }
    }

    protected static Path adaptPath(String path) {
        return adaptPath(Paths.get(path));
    }
}
