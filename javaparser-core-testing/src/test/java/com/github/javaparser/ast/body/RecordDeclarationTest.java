package com.github.javaparser.ast.body;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class RecordDeclarationTest {

    @Test
    void basicGrammarCompiles() {
        /* https://openjdk.java.net/jeps/395#Description */
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());
    }

    @Test
    void basicGrammar() {
        /* https://openjdk.java.net/jeps/395#Description */
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());

        RecordDeclaration recordDeclaration = recordDeclarations.get(0);
        assertTrue(recordDeclaration.isRecordDeclaration());
        assertTrue(recordDeclaration.getImplementedTypes().isEmpty());
        assertTrue(recordDeclaration.getTypeParameters().isEmpty());
        assertTrue(recordDeclaration.getFullyQualifiedName().isPresent());
        assertEquals("Point", recordDeclaration.getFullyQualifiedName().get());
        assertTrue(recordDeclaration.isRecordDeclaration());

        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertFalse(parameters.isEmpty());
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("x", parameter0.getNameAsString());
        assertEquals("int", parameter0.getTypeAsString());
        Parameter parameter1 = parameters.get(1);
        assertEquals("y", parameter1.getNameAsString());
        assertEquals("int", parameter1.getTypeAsString());
    }

    @Test
    void basicRecordPrints() {
        /* https://openjdk.java.net/jeps/395#Description */
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = parseCompilationUnit(s);

        String expected = "" +
                "record Point(int x, int y) {\n" +
                "}\n" +
                "";
        assertEqualsStringIgnoringEol(expected, cu.toString());
    }

    @Test
    void recordWithVarArgs() {
        String s = "record R(T1 c1, Tn... cn){ }";
        CompilationUnit cu = parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());

        RecordDeclaration recordDeclaration = recordDeclarations.get(0);
        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertFalse(parameters.isEmpty());
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("c1", parameter0.getNameAsString());
        assertEquals("T1", parameter0.getTypeAsString());
        assertFalse(parameter0.isVarArgs());
        Parameter parameter1 = parameters.get(1);
        assertEquals("cn", parameter1.getNameAsString());
        assertEquals("Tn", parameter1.getTypeAsString());
        assertTrue(parameter1.isVarArgs());
    }

    @Disabled
    // https://bugs.openjdk.java.net/browse/JDK-8222777
    @Test
    void recordDeclarationFromTheJDK8222777() {
        CompilationUnit cu = parseCompilationUnit("" +
                "public record Range(int lo, int hi) {\n" +
                "\n" +
                "  public Range {\n" +
                "    if (lo > hi)  /* referring here to the implicit constructor parameters */\n" +
                "      throw new IllegalArgumentException(String.format(\"(%d,%d)\", lo, hi));\n" +
                "  }\n" +
                "}"
        );

        RecordDeclaration record = cu.findFirst(RecordDeclaration.class).get();
        assertThat(record.getNameAsString()).isEqualTo("Range");
        assertThat(record.getModifiers()).containsExactly(Modifier.publicModifier());
        // test parameters
        // get constructor
        // test parameters (none)
    }
}
