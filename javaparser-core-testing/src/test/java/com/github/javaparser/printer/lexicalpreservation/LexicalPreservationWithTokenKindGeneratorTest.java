package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.printer.PrettyPrinter;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class LexicalPreservationWithTokenKindGeneratorTest {


    @Test
    public void foo() {
        String originalCode = "" +
                "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
                "\n" +
                "        EOF(0),\n" +
                "        SPACE(1),\n" +
                "        WINDOWS_EOL(2),\n" +
                "        UNIX_EOL(3),\n" +
                "        OLD_MAC_EOL(4),\n" +
                "        SINGLE_LINE_COMMENT(5),\n" +
                "        CTRL_Z(146);\n" +
                "\n" +
                "        private final int kind;\n" +
                "\n" +
                "        Kind(int kind) {\n" +
                "            this.kind = kind;\n" +
                "        }\n" +
                "\n" +
                "        public static Kind valueOf(int kind) {\n" +
                "            switch(kind) {\n" +
                "                case 146:\n" +
                "                    return CTRL_Z;\n" +
                "                case 5:\n" +
                "                    return SINGLE_LINE_COMMENT;\n" +
                "                case 4:\n" +
                "                    return OLD_MAC_EOL;\n" +
                "                case 3:\n" +
                "                    return UNIX_EOL;\n" +
                "                case 2:\n" +
                "                    return WINDOWS_EOL;\n" +
                "                case 1:\n" +
                "                    return SPACE;\n" +
                "                case 0:\n" +
                "                    return EOF;\n" +
                "                default:\n" +
                "                    throw new IllegalArgumentException(f(\"Token kind %i is unknown.\", kind));\n" +
                "            }\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";


        String expectedOutput_lexical = "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
                "\n" +
                "        \n" +
                "\n" +
                "        private final int kind;\n" +
                "\n" +
                "        Kind(int kind) {\n" +
                "            this.kind = kind;\n" +
                "        }\n" +
                "\n" +
                "        public static Kind valueOf(int kind) {\n" +
                "            switch(kind) {\n" +
                "                default:\n" +
                "                    throw new IllegalArgumentException(f(\"Token kind %i is unknown.\", kind));\n" +
                "\n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "                \n" +
                "            }\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";


        ParserConfiguration parserConfiguration = new ParserConfiguration()
                .setLanguageLevel(RAW)
//            .setStoreTokens(false)
//            .setAttributeComments(false)
                .setLexicalPreservationEnabled(true)
                ;

        JavaParser javaParser = new JavaParser(parserConfiguration);

        ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);

        final ClassOrInterfaceDeclaration javaToken = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        final EnumDeclaration kindEnum = javaToken.findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind")).orElseThrow(() -> new AssertionError("Can't find class in java file."));

        List<MethodDeclaration> valueOfMethods = kindEnum.getMethodsByName("valueOf");
        if (valueOfMethods.size() != 1) {
            throw new AssertionError("Expected precisely one method named valueOf");
        }
        MethodDeclaration valueOfMethod = valueOfMethods.get(0);
        final SwitchStmt valueOfSwitch = valueOfMethod.findFirst(SwitchStmt.class).orElseThrow(() -> new AssertionError("Can't find valueOf switch."));


        // TODO: Define "reset"
        // Reset the enum:
        kindEnum.getEntries().clear();
        // Reset the switch within the method valueOf(), leaving only the default
//        valueOfSwitch.getEntries().stream().filter(e -> e.getLabels().isNonEmpty()).forEach(Node::remove);

        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        SwitchEntry defaultEntry = valueOfSwitch.getDefaultSwitchEntry().get();
        valueOfSwitch.getEntries().clear();
        valueOfSwitch.getEntries().add(defaultEntry);


//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(expectedOutput_lexical, LexicalPreservingPrinter.print(javaTokenCu));

    }
}
