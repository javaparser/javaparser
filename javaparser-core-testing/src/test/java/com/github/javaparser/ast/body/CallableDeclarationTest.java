/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class CallableDeclarationTest {

    // A concrete subclass of CallableDeclaration for testing
    private static class ConcreteCallableDeclaration extends CallableDeclaration<ConcreteCallableDeclaration> {
        public ConcreteCallableDeclaration () {
            super(new NodeList<>(), new NodeList<>(), new NodeList<>(), new SimpleName("Test"), new NodeList<>(), new NodeList<>(), null);
        }

        @Override
        public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows, boolean includingParameterName) {
            return null;
        }

        @Override
        public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
            return null;
        }

        @Override
        public <A> void accept(VoidVisitor<A> v, A arg) {

        }
    }

    @Test
    void testConstructor() {
        ConcreteCallableDeclaration decl = new ConcreteCallableDeclaration();
        assertNotNull(decl);
        assertEquals("Test", decl.getName().getIdentifier());
    }

    @Test
    void testRemove() {
        ConcreteCallableDeclaration decl = new ConcreteCallableDeclaration();

        Modifier modToRemove = new Modifier();
        decl.getModifiers().add(modToRemove);
        assertTrue(decl.remove(modToRemove));
        assertFalse(decl.getModifiers().contains(modToRemove));

        Parameter paramToRemove = new Parameter();
        decl.getParameters().add(paramToRemove);
        assertTrue(decl.remove(paramToRemove));
        assertFalse(decl.getParameters().contains(paramToRemove));

        TypeParameter typeParamToRemove = new TypeParameter();
        decl.getTypeParameters().add(typeParamToRemove);
        assertTrue(decl.remove(typeParamToRemove));
        assertFalse(decl.getTypeParameters().contains(typeParamToRemove));
    }

    @Test
    void testReplace() {
        ConcreteCallableDeclaration decl = new ConcreteCallableDeclaration();

        SimpleName newName = new SimpleName("ReplacedTest");
        decl.replace(decl.getName(), newName);
        assertEquals("ReplacedTest", decl.getName().getIdentifier());

        Modifier oldModifier = new Modifier();
        decl.getModifiers().add(oldModifier);
        Modifier newModifier = new Modifier();
        decl.replace(oldModifier, newModifier);
        assertTrue(decl.getModifiers().contains(newModifier));

        Parameter oldParam = new Parameter();
        decl.getParameters().add(oldParam);
        Parameter newParam = new Parameter();
        decl.replace(oldParam, newParam);
        assertTrue(decl.getParameters().contains(newParam));

        TypeParameter oldTypeParam = new TypeParameter();
        decl.getTypeParameters().add(oldTypeParam);
        TypeParameter newTypeParam = new TypeParameter();
        decl.replace(oldTypeParam, newTypeParam);
        assertTrue(decl.getTypeParameters().contains(newTypeParam));
    }

    @Test
    void testVariableArityMethod() {
        ConcreteCallableDeclaration decl = new ConcreteCallableDeclaration();
        Parameter varArgParam = new Parameter(new ArrayType(PrimitiveType.intType()), new SimpleName("args"));
        varArgParam.setVarArgs(true);
        decl.addParameter(varArgParam);
        assertTrue(decl.isVariableArityMethod());
        assertFalse(decl.isFixedArityMethod());
    }

    @Test
    void testFixedArityMethod() {
        ConcreteCallableDeclaration decl = new ConcreteCallableDeclaration();
        decl.addParameter(new Parameter(PrimitiveType.intType(), new SimpleName("arg1")));
        assertFalse(decl.isVariableArityMethod());
        assertTrue(decl.isFixedArityMethod());
    }
}
