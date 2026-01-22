/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CodeGenerationUtils;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;

public abstract class AbstractSymbolResolutionTest {

    @AfterEach
    public void reset() {
        // reset configuration to not potentially disturb others tests.
        // So we have to set specific configuration between each test.
        StaticJavaParser.setConfiguration(
                new ParserConfiguration().setSymbolResolver(symbolResolver(defaultTypeSolver())));
    }

    @AfterAll
    public static void tearDown() {
        // clear internal caches
        JavaParserFacade.clearInstances();
    }

    /**
     * An initial attempt at allowing JDK-specific test cases. It is a work-in-progress, and subject to change.
     * @deprecated <strong>Note that use of TestJdk should be a last-resort, preferably implementing JDK-agnostic tests.</strong>
     */
    @Deprecated
    protected enum TestJdk {
        JDK8(8),
        JDK9(9),
        JDK10(10),
        JDK11(11),
        JDK12(12),
        JDK13(13),
        JDK14(14),
        JDK15(15),
        JDK16(16),
        JDK17(17),
        JDK18(18),
        JDK19(19),
        JDK20(20),
        JDK21(21),
        JDK22(22),
        JDK23(23),
        JDK24(24);

        private final Integer major;

        /**
         * @deprecated <strong>Note that use of TestJdk should be a last-resort, preferably implementing JDK-agnostic tests.</strong>
         */
        @Deprecated
        TestJdk(Integer major) {
            this.major = major;
        }

        /**
         * @deprecated <strong>Note that use of TestJdk should be a last-resort, preferably implementing JDK-agnostic tests.</strong>
         */
        @Deprecated
        public int getMajorVersion() {
            return this.major;
        }

        /**
         * @deprecated <strong>Note that use of TestJdk should be a last-resort, preferably implementing JDK-agnostic tests.</strong>
         */
        @Deprecated
        public static TestJdk getCurrentHostJdk() {
            String javaVersion = System.getProperty("java.version");

            // JavaParser explicitly requires a minimum of JDK8 to build.
            if ("8".equals(javaVersion) || javaVersion.startsWith("1.8") || javaVersion.startsWith("8")) {
                return JDK8;
            } else if ("9".equals(javaVersion) || javaVersion.startsWith("9.")) {
                return JDK9;
            } else if ("10".equals(javaVersion) || javaVersion.startsWith("10.")) {
                return JDK10;
            } else if ("11".equals(javaVersion) || javaVersion.startsWith("11.")) {
                return JDK11;
            } else if ("12".equals(javaVersion) || javaVersion.startsWith("12.")) {
                return JDK12;
            } else if ("13".equals(javaVersion) || javaVersion.startsWith("13.")) {
                return JDK13;
            } else if ("14".equals(javaVersion) || javaVersion.startsWith("14.")) {
                return JDK14;
            } else if ("15".equals(javaVersion) || javaVersion.startsWith("15.")) {
                return JDK15;
            } else if ("16".equals(javaVersion) || javaVersion.startsWith("16.")) {
                return JDK16;
            } else if ("17".equals(javaVersion) || javaVersion.startsWith("17.")) {
                return JDK17;
            } else if ("18".equals(javaVersion) || javaVersion.startsWith("18.")) {
                return JDK18;
            } else if ("19".equals(javaVersion) || javaVersion.startsWith("19.")) {
                return JDK19;
            } else if ("20".equals(javaVersion) || javaVersion.startsWith("20.")) {
                return JDK20;
            } else if ("21".equals(javaVersion) || javaVersion.startsWith("21.")) {
                return JDK21;
            } else if ("22".equals(javaVersion) || javaVersion.startsWith("22.")) {
                return JDK22;
            } else if ("23".equals(javaVersion) || javaVersion.startsWith("23.")) {
                return JDK23;
            } else if ("24".equals(javaVersion) || javaVersion.startsWith("24.")) {
                return JDK24;
            }

            throw new IllegalStateException(
                    "Unable to determine the current version of java running from: " + javaVersion);
        }

        /**
         * @deprecated <strong>Note that use of TestJdk should be a last-resort, preferably implementing JDK-agnostic tests.</strong>
         */
        @Deprecated
        @Override
        public String toString() {
            return "TestJdk{" + "System.getProperty(\"java.version\")="
                    + System.getProperty("java.version") + ",major="
                    + major + '}';
        }
    }

    protected static Path adaptPath(Path path) {
        if (Files.exists(path)) {
            return path.toAbsolutePath();
        }
        Path underSymbolSolver = CodeGenerationUtils.mavenModuleRoot(AbstractSymbolResolutionTest.class)
                .resolve("javaparser-symbol-solver-testing")
                .resolve(path);
        if (Files.exists(underSymbolSolver)) {
            return underSymbolSolver;
        } else {
            throw new IllegalArgumentException("I cannot adapt the path " + path);
        }
    }

    protected static Path adaptPath(String path) {
        return adaptPath(Paths.get(path));
    }

    protected SymbolResolver symbolResolver(TypeSolver typeSolver) {
        return new JavaSymbolSolver(typeSolver);
    }

    protected TypeSolver defaultTypeSolver() {
        return new ReflectionTypeSolver();
    }
}
