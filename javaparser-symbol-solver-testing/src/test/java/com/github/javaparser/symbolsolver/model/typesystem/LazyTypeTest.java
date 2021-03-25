/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import org.junit.jupiter.api.Test;

import java.util.function.Function;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.isNull;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.when;

class LazyTypeTest {

    @Test
    void suppliedShouldOnlyBeCalledOnce() {
        Supplier<ResolvedType> supplier = mock(Supplier.class);
        when(supplier.get()).thenReturn(ResolvedVoidType.INSTANCE);

        LazyType lazyType = new LazyType(supplier);

        // Before initialize the concrete type
        verifyNoInteractions(supplier);
        assertNotNull(lazyType.getType(), "The concrete type should not be initialized at the moment.");

        assertTrue(lazyType.isVoid(), "Should be marked as void when, the concrete type is void.");

        // After initialize the concrete type
        verify(supplier).get();
        assertNotNull(lazyType.getType(), "The concrete type should be present.");
    }

    @Test
    void providerShouldOnlyBeCalledOnce() {
        Function<Void, ResolvedType> provider = mock(Function.class);
        when(provider.apply(null)).thenReturn(ResolvedVoidType.INSTANCE);

        LazyType lazyType = new LazyType(provider);

        // Before initialize the concrete type
        verifyNoInteractions(provider);
        assertNotNull(lazyType.getType(),"The concrete type should not be initialized at the moment.");

        assertTrue(lazyType.isVoid(), "Should be marked as void when, the concrete type is void.");

        // After initialize the concrete type
        verify(provider).apply(isNull());
        assertNotNull(lazyType.getType(), "The concrete type should be present.");
    }

    @Test
    void toStringShouldProvideTheCurrentConcreteValue() {
        LazyType lazyType = new LazyType(() -> ResolvedVoidType.INSTANCE);
        assertTrue(lazyType.toString().contains("concrete=null"));

        assertTrue(lazyType.isVoid());
        assertTrue(lazyType.toString().contains(String.format("concrete=%s", ResolvedVoidType.INSTANCE.toString())));
    }

    @Test
    void whenTwoConcreteTypesAreEqualTheLazyTypeShouldBeEqual() {
        LazyType firstVoidType = new LazyType(() -> ResolvedVoidType.INSTANCE);
        LazyType secondVoidType = new LazyType(() -> ResolvedVoidType.INSTANCE);
        LazyType nestedVoidType = new LazyType(() -> firstVoidType);
        LazyType booleanType = new LazyType(() -> ResolvedPrimitiveType.BOOLEAN);
        LazyType nullReturnType = new LazyType(() -> null);

        assertEquals(firstVoidType, secondVoidType);
        assertEquals(secondVoidType, firstVoidType);
        assertEquals(firstVoidType.hashCode(), secondVoidType.hashCode());
        assertEquals(secondVoidType.hashCode(), firstVoidType.hashCode());

        // Assert nested type are equal
        assertEquals(firstVoidType, nestedVoidType);
        assertEquals(secondVoidType, nestedVoidType);
        assertEquals(nestedVoidType, firstVoidType);
        assertEquals(nestedVoidType, secondVoidType);
        assertEquals(firstVoidType.hashCode(), nestedVoidType.hashCode());
        assertEquals(secondVoidType.hashCode(), nestedVoidType.hashCode());
        assertEquals(nestedVoidType.hashCode(), firstVoidType.hashCode());
        assertEquals(nestedVoidType.hashCode(), secondVoidType.hashCode());


        assertNotEquals(firstVoidType, booleanType);
        assertNotEquals(booleanType, firstVoidType);
        assertNotEquals(firstVoidType.hashCode(), booleanType.hashCode());
        assertNotEquals(booleanType.hashCode(), firstVoidType.hashCode());

        assertNotEquals(nullReturnType, firstVoidType);
        assertNotEquals(firstVoidType, nullReturnType);
    }

}
