/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.utils;

import com.github.javaparser.ast.CompilationUnit;
import com.google.common.jimfs.Configuration;
import com.google.common.jimfs.Jimfs;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.*;

import static com.github.javaparser.utils.CodeGenerationUtils.getterName;
import static com.github.javaparser.utils.CodeGenerationUtils.setterName;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertEquals;

class CodeGenerationUtilsTest {
    @Test
    void setters() {
        assertEquals("setValue", setterName("value"));
        assertEquals("setBlue", setterName("isBlue"));
    }

    @Test
    void getters() {
        assertEquals("getValue", getterName(Object.class, "value"));
        assertEquals("isBlue", getterName(boolean.class, "isBlue"));
        assertEquals("isBlue", getterName(boolean.class, "blue"));
        assertEquals("getBlue", getterName(Boolean.class, "blue"));
        assertEquals("getIsBlue", getterName(Boolean.class, "isBlue"));
    }

    @Nested
    class Parse_from_default_file_system {
        public static final String EXPECTED_SOURCE_CODE =
            "public class HelloWorld {\n" +
                "\n" +
                "    public static void main(String[] args) {\n" +
                "        System.out.println(\"Hello world!\");\n" +
                "    }\n" +
                "}\n";
        private SourceRoot sourceRoot;
        private CompilationUnit compilationUnit;
        private String filename;

        @BeforeEach
        void given_instantiated_dependencies() {
            Path srcPath = Paths.get("src/test/resources");
            sourceRoot = new SourceRoot(srcPath);
            filename = "HelloWorld.java";
        }

        @Test
        void should_parse_HelloWorld_dot_java_from_default_filesystem_having_no_start_package() {
            compilationUnit = sourceRoot.parse("", filename);
            assertThat(compilationUnit.toString()).isEqualTo(EXPECTED_SOURCE_CODE);
        }

        @Test
        void should_parse_HelloWorld_dot_java_from_default_filesystem_having_package_com_dot_github_dot_javaparser() {
            compilationUnit = sourceRoot.parse("com.github.javaparser", filename);
            assertThat(compilationUnit.toString()).isEqualTo("package com.github.javaparser;\n\n" + EXPECTED_SOURCE_CODE);
        }
    }

    @Nested
    class Parse_from_JimFs_file_system {
        public static final String EXPECTED_SOURCE_CODE =
            "public class HelloWorld {\n" +
                "\n" +
                "    public static void main(String[] args) {\n" +
                "        System.out.println(\"Hello world!\");\n" +
                "    }\n" +
                "}\n";
        private FileSystem fileSystem;

        @BeforeEach
        void given_instantiated_dependencies() {
            fileSystem = Jimfs.newFileSystem(Configuration.unix());
        }

        @Test
        void should_parse_HelloWorld_dot_java_from_jimfs_filesystem_having_no_start_package() throws IOException {
            Path srcPath = fileSystem.getPath("/src");
            Files.createDirectory(srcPath);

            Path from = new File("src/test/resources/HelloWorld.java").toPath();
            Path to = srcPath.resolve("HelloWorld.java");
            Files.copy(from, to, StandardCopyOption.REPLACE_EXISTING);

            SourceRoot sourceRoot = new SourceRoot(srcPath);
            CompilationUnit compilationUnit = sourceRoot.parse(to);

            assertThat(compilationUnit.toString()).isEqualTo(EXPECTED_SOURCE_CODE);
        }

        @Test
        void should_parse_HelloWorld_dot_java_from_jimfs_filesystem_having_package_com_dot_github_dot_javaparser() throws IOException {
            Path srcPath = fileSystem.getPath("/src/com/github/javaparser");
            Files.createDirectories(srcPath);

            Path from = new File("src/test/resources/com/github/javaparser/HelloWorld.java").toPath();
            Path to = srcPath.resolve("HelloWorld.java");
            Files.copy(from, to, StandardCopyOption.REPLACE_EXISTING);

            SourceRoot sourceRoot = new SourceRoot(srcPath);
            CompilationUnit compilationUnit = sourceRoot.parse(to);

            assertThat(compilationUnit.toString()).isEqualTo("package com.github.javaparser;\n\n" + EXPECTED_SOURCE_CODE);
        }
    }
}
