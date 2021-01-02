package com.github.javaparser.ast.body;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static org.assertj.core.api.Assertions.assertThat;

public class RecordDeclarationTest {
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
