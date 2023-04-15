/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.types;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

class ResolvedArrayTypeTest extends AbstractResolutionTest {

	JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));

	ResolvedType rByte = getType("class A {java.lang.Byte x;}");
	ResolvedType rShort = getType("class A {java.lang.Short x;}");
	ResolvedType rChar = getType("class A {java.lang.Character x;}");
	ResolvedType rInteger = getType("class A {java.lang.Integer x;}");
	ResolvedType rLong = getType("class A {java.lang.Long x;}");
	ResolvedType rFloat = getType("class A {java.lang.Float x;}");
	ResolvedType rDouble = getType("class A {java.lang.Double x;}");
	ResolvedType rString = getType("class A {java.lang.String x;}");
	ResolvedType rCharSequence = getType("class A {java.lang.CharSequence x;}");
	ResolvedType rObject = getType("class A {java.lang.Object x;}");
	ResolvedType rCloneable = getType("class A {java.lang.Cloneable x;}");
	ResolvedType rSerializable = getType("class A {java.io.Serializable x;}");
	ResolvedType rArrayList = getType("class A {java.util.ArrayList x;}");

	@Test
	// An array of primitive type can be assigned another array of primitive type
	// if primitive type are the same.
	void arrayOfPrimitiveIsAssignableByArrayOfSamePrimitiveType() {
		assertTrue(array(ResolvedPrimitiveType.DOUBLE).isAssignableBy(array(ResolvedPrimitiveType.DOUBLE)));
		assertTrue(array(ResolvedPrimitiveType.FLOAT).isAssignableBy(array(ResolvedPrimitiveType.FLOAT)));
		assertTrue(array(ResolvedPrimitiveType.LONG).isAssignableBy(array(ResolvedPrimitiveType.LONG)));
		assertTrue(array(ResolvedPrimitiveType.INT).isAssignableBy(array(ResolvedPrimitiveType.INT)));
		assertTrue(array(ResolvedPrimitiveType.BYTE).isAssignableBy(array(ResolvedPrimitiveType.BYTE)));
		assertTrue(array(ResolvedPrimitiveType.SHORT).isAssignableBy(array(ResolvedPrimitiveType.SHORT)));
		assertTrue(array(ResolvedPrimitiveType.CHAR).isAssignableBy(array(ResolvedPrimitiveType.CHAR)));
	}

	@Test
	void arrayOfPrimitiveIsNotAssignableByArrayOfDifferentPrimitiveType() {
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.DOUBLE),
				arrays(ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.LONG, ResolvedPrimitiveType.INT,
						ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR)));
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.FLOAT),
				arrays(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.LONG, ResolvedPrimitiveType.INT,
						ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR)));
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.LONG),
				arrays(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.INT,
						ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR)));
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.INT),
				arrays(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.LONG,
						ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR)));
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.BYTE),
				arrays(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.LONG,
						ResolvedPrimitiveType.INT, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR)));
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.SHORT),
				arrays(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.LONG,
						ResolvedPrimitiveType.INT, ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.CHAR)));
		assertFalse(isAssignableBy(array(ResolvedPrimitiveType.CHAR),
				arrays(ResolvedPrimitiveType.DOUBLE, ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.LONG,
						ResolvedPrimitiveType.INT, ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT)));
	}

	@Test
	// An array of primitive type cannot be assigned to a Boxed type variable,
	// because Boxed type is a class type other than Object
	void arrayOfPrimitiveIsNotAssignableByArrayOfBoxedType() {
		assertFalse(array(ResolvedPrimitiveType.DOUBLE).isAssignableBy(array(rDouble)));
		assertFalse(array(ResolvedPrimitiveType.FLOAT).isAssignableBy(array(rFloat)));
		assertFalse(array(ResolvedPrimitiveType.LONG).isAssignableBy(array(rLong)));
		assertFalse(array(ResolvedPrimitiveType.INT).isAssignableBy(array(rInteger)));
		assertFalse(array(ResolvedPrimitiveType.BYTE).isAssignableBy(array(rByte)));
		assertFalse(array(ResolvedPrimitiveType.SHORT).isAssignableBy(array(rShort)));
		assertFalse(array(ResolvedPrimitiveType.CHAR).isAssignableBy(array(rChar)));
	}

	@Test
	void arrayOfPrimitiveIsAssignableByNullType() {
		assertTrue(array(ResolvedPrimitiveType.DOUBLE).isAssignableBy(NullType.INSTANCE));
		assertTrue(array(ResolvedPrimitiveType.FLOAT).isAssignableBy(NullType.INSTANCE));
		assertTrue(array(ResolvedPrimitiveType.LONG).isAssignableBy(NullType.INSTANCE));
		assertTrue(array(ResolvedPrimitiveType.INT).isAssignableBy(NullType.INSTANCE));
		assertTrue(array(ResolvedPrimitiveType.BYTE).isAssignableBy(NullType.INSTANCE));
		assertTrue(array(ResolvedPrimitiveType.SHORT).isAssignableBy(NullType.INSTANCE));
		assertTrue(array(ResolvedPrimitiveType.CHAR).isAssignableBy(NullType.INSTANCE));
	}

	@Test
	// An array can be assigned only to a variable of a compatible array type, or to
	// a variable of type Object, Cloneable or java.io.Serializable.
	void objectIsAssignableByAnyArrayOfPrimitiveTypeOrReference() {
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.DOUBLE)));
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.FLOAT)));
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.LONG)));
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.INT)));
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.BYTE)));
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.SHORT)));
		assertTrue(rObject.isAssignableBy(array(ResolvedPrimitiveType.CHAR)));
		assertTrue(rObject.isAssignableBy(array(rString)));
	}

	@Test
	void cloneableIsAssignableByAnyArrayOfPrimitiveTypeOrReference() {
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.DOUBLE)));
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.FLOAT)));
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.LONG)));
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.INT)));
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.BYTE)));
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.SHORT)));
		assertTrue(rCloneable.isAssignableBy(array(ResolvedPrimitiveType.CHAR)));
		assertTrue(rCloneable.isAssignableBy(array(rString)));
	}

	@Test
	void serializableIsAssignableByAnyArrayOfPrimitiveTypeOrReference() {
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.DOUBLE)));
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.FLOAT)));
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.LONG)));
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.INT)));
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.BYTE)));
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.SHORT)));
		assertTrue(rSerializable.isAssignableBy(array(ResolvedPrimitiveType.CHAR)));
		assertTrue(rSerializable.isAssignableBy(array(rString)));
	}

	@Test
	void arrayOfSubTypeIsAssignableByArrayOfSuperType() {
		assertTrue(array(rCharSequence).isAssignableBy(array(rString)));
	}

	@Test
	void arrayOfReferenceIsNotAssignableByArrayOfOtherReference() {
		assertFalse(array(rString).isAssignableBy(array(rCharSequence)));
	}

	@Test
	void arrayOfObjectIsAssignableByArrayOfReference() {
		assertTrue(array(rObject).isAssignableBy(array(rLong)));
	}

	@Test
	void arrayOfObjectIsNotAssignableByArrayOfPrimitiveType() {
		assertFalse(array(rObject).isAssignableBy(array(ResolvedPrimitiveType.LONG)));
	}

	private boolean isAssignableBy(ResolvedType type, ResolvedType... types) {
		return Arrays.stream(types).anyMatch(t -> type.isAssignableBy(t));
	}

	private ResolvedArrayType[] arrays(ResolvedType... types) {
		return Arrays.stream(types).map(t -> array(t)).collect(Collectors.toList()).toArray(new ResolvedArrayType[] {});
	}

	private ResolvedArrayType array(ResolvedType type) {
		return new ResolvedArrayType(type);
	}

	private ResolvedType getType(String code) {
		return parser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType();
	}

}
