package com.github.javaparser.ast.body;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.opentest4j.AssertionFailedError;

import java.util.List;

import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;

public class RecordDeclarationTest {

    @ParameterizedTest
    @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_13", "JAVA_13_PREVIEW", "JAVA_14", "JAVA_15"})
    void basicGrammarCompiles_languageLevelValidation_forbidden(ParserConfiguration.LanguageLevel languageLevel) {
        String s = "record Point(int x, int y) { }";
        assertThrows(AssertionFailedError.class, () -> {
            CompilationUnit cu = parseCompilationUnit(languageLevel, s);
        });
    }

    @ParameterizedTest
    @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_14_PREVIEW", "JAVA_15_PREVIEW", "JAVA_16", "JAVA_16_PREVIEW"})
    void basicGrammarCompiles_languageLevelValidation_permitted(ParserConfiguration.LanguageLevel languageLevel) {
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = parseCompilationUnit(languageLevel, s);
    }

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
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("x", parameter0.getNameAsString());
        assertEquals("int", parameter0.getTypeAsString());
        Parameter parameter1 = parameters.get(1);
        assertEquals("y", parameter1.getNameAsString());
        assertEquals("int", parameter1.getTypeAsString());

        assertEquals(0, recordDeclaration.getMembers().size());
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

    @Test
    void recordWithAnnotationedParameters() {
        String s = "record Card(@MyAnno Rank rank, @MyAnno Suit suit) { }";
        CompilationUnit cu = parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        assertEquals(1, recordDeclarations.size());

        RecordDeclaration recordDeclaration = recordDeclarations.get(0);
        NodeList<Parameter> parameters = recordDeclaration.getParameters();
        assertEquals(2, parameters.size());

        Parameter parameter0 = parameters.get(0);
        assertEquals("rank", parameter0.getNameAsString());
        assertEquals("Rank", parameter0.getTypeAsString());
        assertEquals(1, parameter0.getAnnotations().size());

        Parameter parameter1 = parameters.get(1);
        assertEquals("suit", parameter1.getNameAsString());
        assertEquals("Suit", parameter1.getTypeAsString());
        assertEquals(1, parameter1.getAnnotations().size());

        assertEquals(0, recordDeclaration.getMembers().size());
    }

    @Test
    void record_emptyMembers() {
        String s = "record Point(int x, int y) { }";
        CompilationUnit cu = parseCompilationUnit(s);

        List<RecordDeclaration> recordDeclarations = cu.findAll(RecordDeclaration.class);
        RecordDeclaration recordDeclaration = recordDeclarations.get(0);

        assertEquals(0, recordDeclaration.getMembers().size());
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
