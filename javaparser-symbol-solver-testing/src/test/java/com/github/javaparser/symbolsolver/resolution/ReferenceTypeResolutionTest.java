/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ReferenceTypeResolutionTest extends AbstractResolutionTest {

    @BeforeEach
    void setup() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);
    }
    
	@Test
	void enumTest() {
	    String code = "enum DAY { MONDAY }";
        ResolvedEnumConstantDeclaration rt = StaticJavaParser.parse(code).findFirst(EnumConstantDeclaration.class).get().resolve();
        assertTrue(rt.isEnumConstant());
	}
	
	@Test
    void objectTest() {
        String code = "class A { Object o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertTrue(rt.isJavaLangObject());
    }
	
	@Test
    void cannotUnboxReferenceTypeTest() {
        String code = "class A { Object o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertFalse(rt.isUnboxable());
    }
	
	@Test
    void unboxableTypeTest() {
        String code = "class A { Integer o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertTrue(rt.asReferenceType().isUnboxable());
    }
	
	@Test
    void cannotUnboxTypeToSpecifiedPrimitiveTypeTest() {
        String code = "class A { Object o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertFalse(rt.isUnboxableTo(ResolvedPrimitiveType.INT));
    }
	
	@Test
    void unboxTypeToSpecifiedPrimitiveTypeTest() {
        String code = "class A { Integer o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertTrue(rt.isUnboxableTo(ResolvedPrimitiveType.INT));
    }
	
	@Test
    void cannotUnboxTypeToPrimitiveTypeTest() {
        String code = "class A { Object o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertFalse(rt.toUnboxedType().isPresent());
    }
	
	@Test
    void unboxTypeToPrimitiveTypeTest() {
        String code = "class A { Integer o; }";
        ResolvedReferenceType rt = StaticJavaParser.parse(code).findFirst(FieldDeclaration.class).get().resolve().getType().asReferenceType();
        assertTrue(rt.toUnboxedType().isPresent());
    }

}
