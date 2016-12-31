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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

import static org.junit.Assert.assertEquals;

/**
 * Transforming ClassOrInterfaceDeclaration and verifying the LexicalPreservation works as expected.
 */
public class ClassOrInterfaceDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected ClassOrInterfaceDeclaration consider(String code) {
        considerCode(code);
        return (ClassOrInterfaceDeclaration)cu.getType(0);
    }

    // Name

    // isInterface;

    // typeParameters;

    //  extendedTypes;

    // implementedTypes;

    // Modifiers

    @Test
    public void addingModifiers() throws IOException {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public class A {}", cid);
    }

    @Test
    public void removingModifiers() throws IOException {
        ClassOrInterfaceDeclaration cid = consider("public class A {}");
        cid.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("class A {}", cid);
    }

    @Test
    public void replacingModifiers() throws IOException {
        ClassOrInterfaceDeclaration cid = consider("public class A {}");
        cid.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected class A {}", cid);
    }

    // members

    // Annotations

    // Javadoc

}
