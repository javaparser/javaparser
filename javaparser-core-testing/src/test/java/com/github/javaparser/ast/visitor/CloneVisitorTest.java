/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.ast.visitor;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseType;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.CompilationUnit.Storage;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.type.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.Iterator;
import java.util.Optional;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

class CloneVisitorTest {
    CompilationUnit cu;

    @BeforeEach
    void setUp() {
        cu = new CompilationUnit();
    }

    @AfterEach
    void teardown() {
        cu = null;
    }

    private static <T> T require(Optional<T> optional) {
        return optional.orElseThrow(AssertionError::new);
    }

    @Test
    void cloneJavaDocTest() {
        NodeList<BodyDeclaration<?>> bodyDeclarationList = new NodeList<>();
        bodyDeclarationList.add(new AnnotationMemberDeclaration().setJavadocComment("javadoc"));
        bodyDeclarationList.add(new ConstructorDeclaration().setJavadocComment("javadoc"));
        bodyDeclarationList.add(new EnumConstantDeclaration().setJavadocComment("javadoc"));
        bodyDeclarationList.add(new FieldDeclaration().setJavadocComment("javadoc"));
        bodyDeclarationList.add(new InitializerDeclaration().setJavadocComment("javadoc"));
        bodyDeclarationList.add(new MethodDeclaration().setJavadocComment("javadoc"));

        NodeList<TypeDeclaration<?>> typeDeclarationList = new NodeList<>();
        AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration();
        annotationDeclaration.setName("nnotationDeclarationTest");
        typeDeclarationList.add(annotationDeclaration.setJavadocComment("javadoc"));

        ClassOrInterfaceDeclaration classOrInterfaceDeclaration2 = new ClassOrInterfaceDeclaration();
        classOrInterfaceDeclaration2.setName("emptyTypeDeclarationTest");
        typeDeclarationList.add(classOrInterfaceDeclaration2.setJavadocComment("javadoc"));

        EnumDeclaration enumDeclaration = new EnumDeclaration();
        enumDeclaration.setName("enumDeclarationTest");
        typeDeclarationList.add(enumDeclaration.setJavadocComment("javadoc"));

        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration();
        classOrInterfaceDeclaration.setName("classOrInterfaceDeclarationTest");
        typeDeclarationList.add(classOrInterfaceDeclaration.setJavadocComment("javadoc"));

        ClassOrInterfaceDeclaration classOrInterfaceDeclaration1 = new ClassOrInterfaceDeclaration();
        classOrInterfaceDeclaration1.setName("emptyTypeDeclarationTest1");
        typeDeclarationList.add(classOrInterfaceDeclaration2.setMembers(bodyDeclarationList));

        cu.setTypes(typeDeclarationList);
        CompilationUnit cuClone = (CompilationUnit) new CloneVisitor().visit(cu, null);

        NodeList<TypeDeclaration<?>> typeDeclarationListClone = cuClone.getTypes();
        Iterator<TypeDeclaration<?>> typeItr = typeDeclarationListClone.iterator();
        TypeDeclaration<?> typeDeclaration;
        while (typeItr.hasNext()) {
            typeDeclaration = typeItr.next();
            if (typeDeclaration.getMembers() == null) {
                assertEquals("javadoc", typeDeclaration.getComment().get().getContent());
            } else {
                Iterator<BodyDeclaration<?>> bodyItr =
                        typeDeclaration.getMembers().iterator();
                while (bodyItr.hasNext()) {
                    BodyDeclaration<?> bodyDeclaration = bodyItr.next();
                    assertEquals("javadoc", bodyDeclaration.getComment().get().getContent());
                }
            }
        }
    }

    @Test
    void cloneAnnotationOnWildcardTypeArgument() {
        Type type = parseType("List<@C ? extends Object>").clone();
        assertEquals("List<@C ? extends Object>", type.toString());
    }

    @Test
    void cloneRecordWithCompactConstructor() {
        JavaParser javaParser = new JavaParser(
                new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_14));
        CompilationUnit original = javaParser
                .parse("record Point(int x, int y) {\n"
                + "    public Point {\n"
                + "        if (x < 0) {\n"
                + "            throw new IllegalArgumentException();\n"
                + "        }\n"
                + "    }\n"
                + "}")
                .getResult()
                .get();

        CompilationUnit cloned = original.clone();

        assertEquals(original.toString(), cloned.toString());
    }

    @Test
    void cloneCompilationUnitKeepsTopLevelStateAndModuleDirectives(@TempDir Path tempDir) throws Exception {
        DataKey<String> testData = new DataKey<String>() {};
        Path source = tempDir.resolve("Example.java");

        cu.setPackageDeclaration("a.b");
        cu.addImport("java.util.List");
        cu.addClass("Example");
        cu.setModule(require(parse("open module com.example {\n"
                        + "    requires transitive java.sql;\n"
                        + "    exports com.example.api to other.module;\n"
                        + "    opens com.example.internal;\n"
                        + "    uses com.example.Service;\n"
                        + "    provides com.example.Service with com.example.impl.ServiceImpl;\n"
                        + "}")
                .getModule()));
        cu.setStorage(source, StandardCharsets.UTF_16);
        cu.addOrphanComment(new LineComment("orphan comment"));
        cu.setData(testData, "metadata");

        CompilationUnit clone = cu.clone();
        ModuleDeclaration originalModule = require(cu.getModule());
        ModuleDeclaration clonedModule = require(clone.getModule());
        Storage clonedStorage = require(clone.getStorage());
        Comment clonedOrphanComment = clone.getOrphanComments().get(0);

        assertNotSame(cu, clone);
        assertEquals("a.b", require(clone.getPackageDeclaration()).getNameAsString());
        assertEquals("java.util.List", clone.getImport(0).getNameAsString());
        assertEquals("Example", clone.getType(0).getNameAsString());
        assertEquals(originalModule.toString(), clonedModule.toString());
        assertNotSame(originalModule, clonedModule);
        assertSame(clone, require(clonedModule.getParentNode()));
        assertEquals(source.toAbsolutePath(), clonedStorage.getPath());
        assertEquals(StandardCharsets.UTF_16, clonedStorage.getEncoding());
        assertSame(clone, clonedStorage.getCompilationUnit());
        assertEquals("orphan comment", clonedOrphanComment.getContent());
        assertNotSame(cu.getOrphanComments().get(0), clonedOrphanComment);
        assertSame(clone, require(clonedOrphanComment.getParentNode()));
        assertEquals("metadata", clone.getData(testData));
    }
}
