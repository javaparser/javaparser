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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.description.JavadocDescription;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.Ignore;
import org.junit.Test;

import java.util.EnumSet;

import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

/**
 * Transforming MethodDeclaration and verifying the LexicalPreservation works as expected.
 */
public class MethodDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected MethodDeclaration consider(String code) {
        considerCode("class A { " + code + " }");
        return cu.getType(0).getMembers().get(0).asMethodDeclaration();
    }

    // Name

    @Test
    public void settingName() {
        MethodDeclaration it = consider("void A(){}");
        it.setName("B");
        assertTransformedToString("void B(){}", it);
    }

    // JavaDoc

    @Ignore("Indentation not correct yet")
    @Test
    public void removingDuplicateJavaDocComment() {
        // Arrange
        considerCode("public class MyClass {" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void oneMethod() {" + EOL +
                "  }" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void anotherMethod() {" + EOL +
                "  }" + EOL +
                "}" +
                EOL);

        MethodDeclaration methodDeclaration = cu.findAll(MethodDeclaration.class).get(1);

        // Act
        methodDeclaration.removeComment();

        // Assert
        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("public class MyClass {\n" +
                "\n" +
                "  /**\n" +
                "   * Comment A\n" +
                "   */\n" +
                "  public void oneMethod() {\n" +
                "  }\n" +
                "\n" +
                "  public void anotherMethod() {\n" +
                "  }\n" +
                "}\n", result);
    }

    @Ignore("Indentation not correct yet")
    @Test
    public void replacingDuplicateJavaDocComment() {
        // Arrange
        considerCode("public class MyClass {" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void oneMethod() {" + EOL +
                "  }" + EOL +
                EOL +
                "  /**" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void anotherMethod() {" + EOL +
                "  }" + EOL +
                "}" +
                EOL);

        MethodDeclaration methodDeclaration = cu.findAll(MethodDeclaration.class).get(1);

        // Act
        Javadoc javadoc = new Javadoc(JavadocDescription.parseText("Change Javadoc"));
        methodDeclaration.setJavadocComment("", javadoc);

        // Assert
        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("public class MyClass {\n" +
                "\n" +
                "  /**\n" +
                "   * Comment A\n" +
                "   */\n" +
                "  public void oneMethod() {\n" +
                "  }\n" +
                "\n" +
                "  /**\n" +
                "   * Change Javadoc\n" +
                "   */\n" +
                "  public void anotherMethod() {\n" +
                "  }\n" +
                "}\n", result);
    }

    // Comments

    @Ignore("Comments not supported yet")
    @Test
    public void removingDuplicateComment() {
        // Arrange
        considerCode("public class MyClass {" + EOL +
                EOL +
                "  /*" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void oneMethod() {" + EOL +
                "  }" + EOL +
                EOL +
                "  /*" + EOL +
                "   * Comment A" + EOL +
                "   */" + EOL +
                "  public void anotherMethod() {" + EOL +
                "  }" + EOL +
                "}" +
                EOL);

        MethodDeclaration methodDeclaration = cu.findAll(MethodDeclaration.class).get(1);

        // Act
        methodDeclaration.removeComment();

        // Assert
        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("public class MyClass {\n" +
                "\n" +
                "  /*\n" +
                "   * Comment A\n" +
                "   */\n" +
                "  public void oneMethod() {\n" +
                "  }\n" +
                "\n" +
                "  public void anotherMethod() {\n" +
                "  }\n" +
                "}\n", result);
    }

    // Modifiers

    @Test
    public void addingModifiers() {
        MethodDeclaration it = consider("void A(){}");
        it.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public void A(){}", it);
    }

    @Test
    public void removingModifiers() {
        MethodDeclaration it = consider("public void A(){}");
        it.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("void A(){}", it);
    }

    @Test
    public void removingModifiersWithExistingAnnotationsShort() {
        MethodDeclaration it = consider("@Override public void A(){}");
        it.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("@Override void A(){}", it);
    }

    @Test
    public void removingModifiersWithExistingAnnotations() {
        considerCode(
                "class X {" + EOL +
                        "  @Test" + EOL +
                        "  public void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).setModifiers(EnumSet.noneOf(Modifier.class));

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("class X {\n" +
                "  @Test\n" +
                "  void testCase() {\n" +
                "  }\n" +
                "}\n", result);
    }

    @Test
    public void replacingModifiers() {
        MethodDeclaration it = consider("public void A(){}");
        it.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected void A(){}", it);
    }

    @Test
    public void replacingModifiersWithExistingAnnotationsShort() {
        MethodDeclaration it = consider("@Override public void A(){}");
        it.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("@Override protected void A(){}", it);
    }

    @Test
    public void replacingModifiersWithExistingAnnotations() {
        considerCode(
                "class X {" + EOL +
                        "  @Test" + EOL +
                        "  public void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).setModifiers(EnumSet.of(Modifier.PROTECTED));

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("class X {\n" +
                "  @Test\n" +
                "  protected void testCase() {\n" +
                "  }\n" +
                "}\n", result);
    }

    // Parameters

    @Test
    public void addingParameters() {
        MethodDeclaration it = consider("void foo(){}");
        it.addParameter(PrimitiveType.doubleType(), "d");
        assertTransformedToString("void foo(double d){}", it);
    }

    @Test
    public void removingOnlyParameter() {
        MethodDeclaration it = consider("public void foo(double d){}");
        it.getParameters().remove(0);
        assertTransformedToString("public void foo(){}", it);
    }

    @Test
    public void removingFirstParameterOfMany() {
        MethodDeclaration it = consider("public void foo(double d, float f){}");
        it.getParameters().remove(0);
        assertTransformedToString("public void foo(float f){}", it);
    }

    @Test
    public void removingLastParameterOfMany() {
        MethodDeclaration it = consider("public void foo(double d, float f){}");
        it.getParameters().remove(1);
        assertTransformedToString("public void foo(double d){}", it);
    }

    @Test
    public void replacingOnlyParameter() {
        MethodDeclaration it = consider("public void foo(float f){}");
        it.getParameters().set(0, new Parameter(new ArrayType(PrimitiveType.intType()), new SimpleName("foo")));
        assertTransformedToString("public void foo(int[] foo){}", it);
    }

    // ThrownExceptions

    // Body

    // Annotations
    @Test
    public void addingToExistingAnnotations() {
        considerCode(
                "class X {" + EOL +
                        "  @Test" + EOL +
                        "  public void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).addSingleMemberAnnotation(
                "org.junit.Ignore",
                new StringLiteralExpr("flaky test"));

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("class X {\n" +
                "  @Test\n" +
                "  @org.junit.Ignore(\"flaky test\")\n" +
                "  public void testCase() {\n" +
                "  }\n" +
                "}\n", result);
    }

    @Test
    public void addingAnnotationsNoModifiers() {
        considerCode(
                "class X {" + EOL +
                        "  void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).addMarkerAnnotation("Test");
        cu.getType(0).getMethods().get(0).addMarkerAnnotation("Override");

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol("class X {\n" +
                "  @Test\n" +
                "  @Override\n" +
                "  void testCase() {\n" +
                "  }\n" +
                "}\n", result);
    }

    @Test
    public void replacingAnnotations() {
        considerCode(
                "class X {" + EOL +
                        "  @Override" + EOL +
                        "  public void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).setAnnotations(new NodeList<>(new MarkerAnnotationExpr("Test")));

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol(
                "class X {\n" +
                        "  @Test\n" +
                        "  public void testCase() {\n" +
                        "  }\n" +
                        "}\n", result);
    }

    @Test
    public void addingAnnotationsShort() {
        MethodDeclaration it = consider("void testMethod(){}");
        it.addMarkerAnnotation("Override");
        assertTransformedToString(
                "@Override" + EOL +
                "void testMethod(){}", it);
    }

    @Test
    public void removingAnnotations() {
        considerCode(
                "class X {" + EOL +
                        "  @Override" + EOL +
                        "  public void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).getAnnotationByName("Override").get().remove();

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol(
                "class X {\n" +
                        "  public void testCase() {\n" +
                        "  }\n" +
                        "}\n", result);
    }

    @Ignore
    @Test
    public void removingAnnotationsWithSpaces() {
        considerCode(
                "class X {" + EOL +
                        "  @Override " + EOL +
                        "  public void testCase() {" + EOL +
                        "  }" + EOL +
                        "}" + EOL
        );

        cu.getType(0).getMethods().get(0).getAnnotationByName("Override").get().remove();

        String result = LexicalPreservingPrinter.print(cu.findCompilationUnit().get());
        assertEqualsNoEol(
                "class X {\n" +
                        "  public void testCase() {\n" +
                        "  }\n" +
                        "}\n", result);
    }
}
