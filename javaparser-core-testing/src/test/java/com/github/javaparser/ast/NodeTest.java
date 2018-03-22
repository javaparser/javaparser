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

package com.github.javaparser.ast;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.JavaParser.parseExpression;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.*;

public class NodeTest {

    @Test
    public void registerSubTree() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.registerForSubtree(observer);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);
    }

    @Test
    public void registerWithJustNodeMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").get().register(observer, Node.ObserverRegistrationMode.JUST_THIS_NODE);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").get().addField("int", "bar").getVariables().get(0).setInitializer("0");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);
    }

    @Test
    public void registerWithNodeAndExistingDescendantsMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").get().register(observer, Node.ObserverRegistrationMode.THIS_NODE_AND_EXISTING_DESCENDANTS);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);

        cu.getClassByName("MyCoolClass").get().addField("int", "bar").getVariables().get(0).setInitializer("0");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);
    }

    @Test
    public void registerWithSelfPropagatingMode() {
        String code = "class A { int f; void foo(int p) { return 'z'; }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
            }
        };
        cu.getClassByName("A").get().register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        assertEquals(Arrays.asList(), changes);

        cu.getClassByName("A").get().setName("MyCoolClass");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass"), changes);

        cu.getClassByName("MyCoolClass").get().getFieldByName("f").get().getVariable(0).setType(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN));
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean"), changes);

        cu.getClassByName("MyCoolClass").get().getMethodsByName("foo").get(0).getParameterByName("p").get().setName("myParam");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam"), changes);

        cu.getClassByName("MyCoolClass").get()
                .addField("int", "bar")
                .getVariables().get(0).setInitializer("0");
        assertEquals(Arrays.asList("ClassOrInterfaceDeclaration.name changed from A to MyCoolClass",
                "FieldDeclaration.maximum_common_type changed from int to boolean",
                "VariableDeclarator.type changed from int to boolean",
                "Parameter.name changed from p to myParam",
                "VariableDeclarator.initializer changed from null to 0"), changes);
    }

    @Test
    public void deleteAParameterTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        cu.getClassByName("A").get().getMethodsByName("foo").get(0).getParameter(0).remove();
        assertEquals(Arrays.asList("removing [int p] from index 0"), changes);
    }

    @Test
    public void deleteClassNameDoesNotTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        // I cannot remove the name of a type
        assertEquals(false, cu.getClassByName("A").get().getName().remove());
        assertEquals(Arrays.asList(), changes);
    }

    @Test
    public void deleteMethodBodyDoesTriggerNotifications() {
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = parse(code);
        List<String> changes = new ArrayList<>();
        AstObserver observer = new AstObserverAdapter() {

            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add("setting [" + property + "] to " + newValue);
            }

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add("removing [" + nodeAddedOrRemoved + "] from index " + index);
            }
        };
        cu.register(observer, Node.ObserverRegistrationMode.SELF_PROPAGATING);

        assertEquals(true, cu.getClassByName("A").get().getMethodsByName("foo").get(0).getBody().get().remove());
        assertEquals(Arrays.asList("setting [BODY] to null"), changes);
    }

    @Test
    public void removeOrphanCommentPositiveCase() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class), false, "A");
        Comment c = new LineComment("A comment");
        decl.addOrphanComment(c);
        assertEquals(1, decl.getOrphanComments().size());
        assertTrue(decl == c.getParentNode().get());
        assertTrue(decl.removeOrphanComment(c));
        assertEquals(0, decl.getOrphanComments().size());
        assertFalse(c.getParentNode().isPresent());
    }

    @Test
    public void removeOrphanCommentNegativeCase() {
        ClassOrInterfaceDeclaration aClass = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class), false, "A");
        FieldDeclaration aField = new FieldDeclaration(EnumSet.noneOf(Modifier.class), new VariableDeclarator(PrimitiveType.intType(), "f"));
        aClass.getMembers().add(aField);
        Comment c = new LineComment("A comment");
        aField.addOrphanComment(c);
        // the comment is an orphan comment of the field, so trying to remove it on the class should not work
        assertFalse(aClass.removeOrphanComment(c));
        assertEquals(1, aField.getOrphanComments().size());
        assertTrue(c.getParentNode().isPresent());
    }

    @Test
    public void hasJavaDocCommentPositiveCaseWithSetJavaDocComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class),
                false, "Foo");
        decl.setJavadocComment("A comment");
        assertEquals(true, decl.hasJavaDocComment());
    }

    @Test
    public void hasJavaDocCommentPositiveCaseWithSetComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class),
                false, "Foo");
        decl.setComment(new JavadocComment("A comment"));
        assertEquals(true, decl.hasJavaDocComment());
    }

    @Test
    public void hasJavaDocCommentNegativeCaseNoComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class),
                false, "Foo");
        assertEquals(false, decl.hasJavaDocComment());
    }

    @Test
    public void hasJavaDocCommentNegativeCaseLineComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class),
                false, "Foo");
        decl.setComment(new LineComment("foo"));
        assertEquals(false, decl.hasJavaDocComment());
    }

    @Test
    public void hasJavaDocCommentNegativeCaseBlockComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(EnumSet.noneOf(Modifier.class),
                false, "Foo");
        decl.setComment(new BlockComment("foo"));
        assertEquals(false, decl.hasJavaDocComment());
    }

    @Test
    public void removeAllOnRequiredProperty() {
        CompilationUnit cu = parse("class X{ void x(){}}");
        MethodDeclaration methodDeclaration = cu.getType(0).getMethods().get(0);
        methodDeclaration.getName().removeForced();
        // Name is required, so to remove it the whole method is removed.
        assertEquals(String.format("class X {%1$s}%1$s", EOL), cu.toString());
    }

    @Test
    public void removingTheSecondOfAListOfIdenticalStatementsDoesNotMessUpTheParents() {
        CompilationUnit unit = parse(String.format("public class Example {%1$s" +
                "  public static void example() {%1$s" +
                "    boolean swapped;%1$s" +
                "    swapped=false;%1$s" +
                "    swapped=false;%1$s" +
                "  }%1$s" +
                "}%1$s", EOL));
        // remove the second swapped=false
        Node target = unit.getChildNodes().get(0).getChildNodes().get(1).getChildNodes().get(2).getChildNodes().get(2);
        target.remove();
        // This will throw an exception if the parents are bad.
        System.out.println(unit.toString());
    }

    @Test
    public void findCompilationUnit() {
        CompilationUnit cu = parse("class X{int x;}");
        VariableDeclarator x = cu.getClassByName("X").get().getMember(0).asFieldDeclaration().getVariables().get(0);
        assertEquals(cu, x.findCompilationUnit().get());
    }

    @Test
    public void findParent() {
        CompilationUnit cu = parse("class X{int x;}");
        SimpleName x = cu.getClassByName("X").get().getMember(0).asFieldDeclaration().getVariables().get(0).getName();
        assertEquals("int x;", x.findParent(FieldDeclaration.class).get().toString());
    }

    @Test
    public void cantFindCompilationUnit() {
        VariableDeclarator x = new VariableDeclarator();
        assertFalse(x.findCompilationUnit().isPresent());
    }

    @Test
    public void genericWalk() {
        Expression e = parseExpression("1+1");
        StringBuilder b = new StringBuilder();
        e.walk(n -> b.append(n.toString()));
        assertEquals("1 + 111", b.toString());
    }

    @Test
    public void classSpecificWalk() {
        Expression e = parseExpression("1+1");
        StringBuilder b = new StringBuilder();
        e.walk(IntegerLiteralExpr.class, n -> b.append(n.toString()));
        assertEquals("11", b.toString());
    }

    @Test
    public void conditionalFindAll() {
        Expression e = parseExpression("1+2+3");
        List<IntegerLiteralExpr> ints = e.findAll(IntegerLiteralExpr.class, n -> n.asInt() > 1);
        assertEquals("[2, 3]", ints.toString());
    }

    @Test
    public void typeOnlyFindAll() {
        Expression e = parseExpression("1+2+3");
        List<IntegerLiteralExpr> ints = e.findAll(IntegerLiteralExpr.class);
        assertEquals("[1, 2, 3]", ints.toString());
    }

    @Test
    public void typeOnlyFindAllMatchesSubclasses() {
        Expression e = parseExpression("1+2+3");
        List<Node> ints = e.findAll(Node.class);
        assertEquals("[1 + 2 + 3, 1 + 2, 1, 2, 3]", ints.toString());
    }

    @Test
    public void conditionalTypedFindFirst() {
        Expression e = parseExpression("1+2+3");
        Optional<IntegerLiteralExpr> ints = e.findFirst(IntegerLiteralExpr.class, n -> n.asInt() > 1);
        assertEquals("Optional[2]", ints.toString());
    }

    @Test
    public void typeOnlyFindFirst() {
        Expression e = parseExpression("1+2+3");
        Optional<IntegerLiteralExpr> ints = e.findFirst(IntegerLiteralExpr.class);
        assertEquals("Optional[1]", ints.toString());
    }
    
    @Test
    public void stream() {
        Expression e = parseExpression("1+2+3");
        List<IntegerLiteralExpr> ints = e.stream()
                .filter(n -> n instanceof IntegerLiteralExpr)
                .map(IntegerLiteralExpr.class::cast)
                .filter(i -> i.asInt() > 1)
                .collect(Collectors.toList());
        assertEquals("[2, 3]", ints.toString());
    }
}
