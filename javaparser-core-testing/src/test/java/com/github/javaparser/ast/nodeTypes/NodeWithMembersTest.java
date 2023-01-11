/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2022 The JavaParser Team.
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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.ObservableProperty;
import org.junit.jupiter.api.Test;

import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.ast.Modifier.Keyword.PRIVATE;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.Keyword.STATIC;
import static com.github.javaparser.ast.Modifier.Keyword.SYNCHRONIZED;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static org.junit.jupiter.api.Assertions.assertEquals;

class NodeWithMembersTest {

    @Test
    void addFieldAtLocationWorks() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        decl.addField("int", "bar");
        decl.addField("int", "c");
        decl.addMethod("testing");
        decl.addMethod("stillTesting");
        // This one below should add it at the end of the class overall
        FieldDeclaration a1 = decl.addFieldAtLocation("String", "a1", decl.getMembers().size()-1,
                NodeWithMembers.LocationType.ALL, true);
        assertEquals(decl.getMember(decl.getMembers().size() -1), a1);

        // Adding it before the end of the fields! This notably should be in the "2" position in them
        FieldDeclaration a2 = decl.addFieldAtLocation("String", "a2", decl.getFields().size()-1,
                NodeWithMembers.LocationType.FIELD, false);
        assertEquals(decl.getFields().get(2), a2);
    }

    @Test
    void addMethodAtLocationWorks() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        decl.addField("int", "bar");
        decl.addField("int", "c");
        decl.addMethod("testing");
        decl.addMethod("stillTesting");
        // Adding it one before the last element in the class
        MethodDeclaration a1 = decl.addMethodAtLocation("a1", decl.getMembers().size()-1,
                NodeWithMembers.LocationType.ALL, false);
        assertEquals(decl.getMember(decl.getMembers().size() - 2), a1);

        // Adding it in between the other two methods
        MethodDeclaration a2 = decl.addMethodAtLocation("a2", 1,
                NodeWithMembers.LocationType.METHOD, true);
        assertEquals(decl.getMethods().get(2), a2);
    }

}
