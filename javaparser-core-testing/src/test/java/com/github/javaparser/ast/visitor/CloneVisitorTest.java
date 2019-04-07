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

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Iterator;

import static com.github.javaparser.StaticJavaParser.parseType;
import static org.junit.jupiter.api.Assertions.assertEquals;

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
                Iterator<BodyDeclaration<?>> bodyItr = typeDeclaration.getMembers().iterator();
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

}
