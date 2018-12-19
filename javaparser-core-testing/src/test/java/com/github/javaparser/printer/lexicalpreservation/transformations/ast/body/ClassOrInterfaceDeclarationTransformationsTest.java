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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast.body;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

import static com.github.javaparser.JavaParser.parseClassOrInterfaceType;
import static com.github.javaparser.utils.Utils.EOL;

/**
 * Transforming ClassOrInterfaceDeclaration and verifying the LexicalPreservation works as expected.
 */
public class ClassOrInterfaceDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected ClassOrInterfaceDeclaration consider(String code) {
        considerCode(code);
        return cu.getType(0).asClassOrInterfaceDeclaration();
    }

    // Name

    @Test
    public void settingName() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.setName("B");
        assertTransformedToString("class B {}", cid);
    }

    // isInterface

    @Test
    public void classToInterface() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.setInterface(true);
        assertTransformedToString("interface A {}", cid);
    }

    @Test
    public void interfaceToClass() {
        ClassOrInterfaceDeclaration cid = consider("interface A {}");
        cid.setInterface(false);
        assertTransformedToString("class A {}", cid);
    }

    // typeParameters

    @Test
    public void addingTypeParameterWhenThereAreNone() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.addTypeParameter("T");
        assertTransformedToString("class A<T> {}", cid);
    }

    @Test
    public void addingTypeParameterAsFirstWhenThereAreSome() {
        ClassOrInterfaceDeclaration cid = consider("class A<U> {}");
        cid.getTypeParameters().addFirst(new TypeParameter("T", new NodeList<>()));
        assertTransformedToString("class A<T, U> {}", cid);
    }

    @Test
    public void addingTypeParameterAsLastWhenThereAreSome() {
        ClassOrInterfaceDeclaration cid = consider("class A<U> {}");
        cid.addTypeParameter("T");
        assertTransformedToString("class A<U, T> {}", cid);
    }

    // extendedTypes

    @Test
    public void addingExtendedTypes() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.addExtendedType("Foo");
        assertTransformedToString("class A extends Foo {}", cid);
    }

    @Test
    public void removingExtendedTypes() {
        ClassOrInterfaceDeclaration cid = consider("public class A extends Foo {}");
        cid.getExtendedTypes().remove(0);
        assertTransformedToString("public class A {}", cid);
    }

    @Test
    public void replacingExtendedTypes() {
        ClassOrInterfaceDeclaration cid = consider("public class A extends Foo {}");
        cid.getExtendedTypes().set(0, parseClassOrInterfaceType("Bar"));
        assertTransformedToString("public class A extends Bar {}", cid);
    }

    // implementedTypes

    @Test
    public void addingImplementedTypes() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.addImplementedType("Foo");
        assertTransformedToString("class A implements Foo {}", cid);
    }

    @Test
    public void removingImplementedTypes() {
        ClassOrInterfaceDeclaration cid = consider("public class A implements Foo {}");
        cid.getImplementedTypes().remove(0);
        assertTransformedToString("public class A {}", cid);
    }

    @Test
    public void replacingImplementedTypes() {
        ClassOrInterfaceDeclaration cid = consider("public class A implements Foo {}");
        cid.getImplementedTypes().set(0, parseClassOrInterfaceType("Bar"));
        assertTransformedToString("public class A implements Bar {}", cid);
    }

    // Modifiers

    @Test
    public void addingModifiers() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public class A {}", cid);
    }

    @Test
    public void removingModifiers() {
        ClassOrInterfaceDeclaration cid = consider("public class A {}");
        cid.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("class A {}", cid);
    }

    @Test
    public void replacingModifiers() {
        ClassOrInterfaceDeclaration cid = consider("public class A {}");
        cid.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected class A {}", cid);
    }

    // members

    @Test
    public void addingField() {
        ClassOrInterfaceDeclaration cid = consider("class A {}");
        cid.addField("int", "foo");
        assertTransformedToString("class A {" + EOL + "    int foo;" + EOL + "}", cid);
    }

    @Test
    public void removingField() {
        ClassOrInterfaceDeclaration cid = consider("public class A { int foo; }");
        cid.getMembers().remove(0);
        assertTransformedToString("public class A {}", cid);
    }

    @Test
    public void replacingFieldWithAnotherField() {
        ClassOrInterfaceDeclaration cid = consider("public class A {float f;}");
        cid.getMembers().set(0, new FieldDeclaration(EnumSet.noneOf(Modifier.class), new VariableDeclarator(PrimitiveType.intType(), "bar")));
        assertTransformedToString("public class A {int bar;}", cid);
    }

    // Annotations
    @Test
    public void removingAnnotations() {
        ClassOrInterfaceDeclaration cid = consider(
                "@Value" + EOL +
                "public class A {}");
        cid.getAnnotationByName("Value").get().remove();
        assertTransformedToString("public class A {}", cid);
    }

    @Test
    public void removingAnnotationsWithSpaces() {
        ClassOrInterfaceDeclaration cid = consider(
                  "   @Value " + EOL +
                        "public class A {}");
        cid.getAnnotationByName("Value").get().remove();
        assertTransformedToString("public class A {}", cid);
    }

    // Javadoc

}
