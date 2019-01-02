package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.Node.Parsedness.UNPARSABLE;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ParseErrorRecoveryTest {
    private final JavaParser parser = new JavaParser();

    @Test
    void compilationUnitRecovery() {
        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, provider("XXX")).getResult().get();
        assertEquals(UNPARSABLE, cu.getParsed());
    }

    @Test
    void bodystatementSemicolonRecovery() {
        MethodDeclaration cu = parser.parse(ParseStart.CLASS_BODY, provider("int x(){X X X;}")).getResult().get().asMethodDeclaration();
        Statement xxx = cu.getBody().get().getStatements().get(0);
        assertEquals(UNPARSABLE, xxx.getParsed());
    }

    @Test
    void bodystatementClosingBraceRecovery() {
        MethodDeclaration cu = parser.parse(ParseStart.CLASS_BODY, provider("int x(){X X X}")).getResult().get().asMethodDeclaration();
        Statement xxx = cu.getBody().get();
        assertEquals(UNPARSABLE, xxx.getParsed());
    }

    @Test
    void labeledStatementSemicolonRecovery() {
        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, provider("class X{int x(){aaa:X X X;}}")).getResult().get();
        LabeledStmt xxx = cu.getClassByName("X").get().getMethods().get(0).getBody().get().getStatements().get(0).asLabeledStmt();
        assertEquals(UNPARSABLE, xxx.getStatement().getParsed());
    }
}
