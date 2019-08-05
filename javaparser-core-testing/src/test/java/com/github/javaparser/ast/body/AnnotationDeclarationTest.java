package com.github.javaparser.ast.body;

import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class AnnotationDeclarationTest {
    @Test
    void cantAddField() {
        assertThrows(IllegalStateException.class, () -> new AnnotationDeclaration().addField(Object.class, "oo"));
    }

    @Test
    void issue2216() {
        Statement statement = parseStatement("TT tt = new <String> @TypeAnno @TA2 TT( \"S\" );");
        assertEquals("TT tt = new <String> @TypeAnno @TA2 TT(\"S\");", statement.toString());
    }
}
