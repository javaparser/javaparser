package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * See issue #17
 */
public class ArrayExprTest {

    @Test
    public void verifyAnArrayAccessExprTypeIsCalculatedProperly() {
        String code = "class A { String[] arrSQL; String toExamine = arrSQL[1]; }";
        FieldDeclaration field = JavaParser.parse(code).getClassByName("A").get().getFieldByName("toExamine").get();

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(field.getVariables().get(0).getInitializer().get());
        assertEquals(true, type.isReferenceType());
        assertEquals("java.lang.String", type.asReferenceType().getQualifiedName());
    }
}
