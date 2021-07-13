package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

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
