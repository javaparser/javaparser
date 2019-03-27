package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.types.ResolvedType;
import org.junit.jupiter.api.Test;

import java.util.stream.Stream;

import static com.github.javaparser.resolution.types.ResolvedPrimitiveType.BOOLEAN;
import static com.github.javaparser.resolution.types.ResolvedPrimitiveType.INT;
import static org.junit.jupiter.api.Assertions.assertEquals;

class MultipleResultTypesLogicTest {
    private final MultipleResultTypesLogic logic = new MultipleResultTypesLogic();

    @Test
    void testNoResultsIsVoid() {
        ResolvedType resultType = logic.findResultType(Stream.of());
        assertEquals("void", resultType.describe());
    }

    @Test
    void testOneResultIsThatResult() {
        ResolvedType resultType = logic.findResultType(Stream.of(INT));
        assertEquals("int", resultType.describe());
    }

    @Test
    void testTwoResultsIsAUnionOfThoseResults() {
        ResolvedType resultType = logic.findResultType(Stream.of(INT, BOOLEAN));
        assertEquals("boolean | int", resultType.describe());
    }

    @Test
    void testDuplicatesAreRemoved() {
        ResolvedType resultType = logic.findResultType(Stream.of(INT, INT, BOOLEAN, BOOLEAN));
        assertEquals("boolean | int", resultType.describe());
    }
}