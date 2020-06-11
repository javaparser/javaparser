package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class LexicalPreservationWithTokenKindGeneratorTest {


    @Test
    public void foo_enumOnly() {
        final String originalCode = "" +
                "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
//                "\n" +
//                "        EOF(0),\n" +
//                "        SPACE(1),\n" +
//                "        WINDOWS_EOL(2),\n" +
//                "        UNIX_EOL(3),\n" +
//                "        OLD_MAC_EOL(4),\n" +
//                "        SINGLE_LINE_COMMENT(5),\n" +
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


        final String expectedOutput_lexical = "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
                "\n" +
//                "        \n" +
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

        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(RAW)
                .setLexicalPreservationEnabled(true)
        );

        final ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        final CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);
        final ClassOrInterfaceDeclaration javaTokenCoid = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final EnumDeclaration kindEnum = javaTokenCoid
                .findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind"))
                .orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final MethodDeclaration valueOfMethodDeclaration = kindEnum.getMethodsByName("valueOf").get(0);
        final SwitchStmt valueOfSwitch = valueOfMethodDeclaration
                .findFirst(SwitchStmt.class)
                .orElseThrow(() -> new AssertionError("Can't find valueOf switch."));


        // Reset the enum:
        kindEnum.getEntries().clear();

//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(expectedOutput_lexical, LexicalPreservingPrinter.print(javaTokenCu));

    }

    @Test
    public void foo_switchOnly() {
        final String originalCode = "" +
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


        final String expectedOutput_lexical = "public class JavaToken {\n" +
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
                "                default:\n" +
                "                    throw new IllegalArgumentException(f(\"Token kind %i is unknown.\", kind));\n" +
//                "\n" +
//                "                \n" +
//                "                \n" +
//                "                \n" +
//                "                \n" +
//                "                \n" +
//                "                \n" +
//                "                \n" +
                "            }\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";

        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(RAW)
                .setLexicalPreservationEnabled(true)
        );

        final ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        final CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);
        final ClassOrInterfaceDeclaration javaTokenCoid = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final EnumDeclaration kindEnum = javaTokenCoid
                .findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind"))
                .orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final MethodDeclaration valueOfMethodDeclaration = kindEnum.getMethodsByName("valueOf").get(0);
        final SwitchStmt valueOfSwitch = valueOfMethodDeclaration
                .findFirst(SwitchStmt.class)
                .orElseThrow(() -> new AssertionError("Can't find valueOf switch."));


        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        final SwitchEntry defaultEntry = valueOfSwitch.getDefaultSwitchEntry().get();
        valueOfSwitch.getEntries().clear();
        valueOfSwitch.getEntries().add(defaultEntry);


//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(expectedOutput_lexical, LexicalPreservingPrinter.print(javaTokenCu));

    }


    @Test
    public void foo_replaceSwitchOnly() {
        final String originalCode = "" +
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
//                "                case 146:\n" +
//                "                    return CTRL_Z;\n" +
//                "                case 5:\n" +
//                "                    return SINGLE_LINE_COMMENT;\n" +
//                "                case 4:\n" +
//                "                    return OLD_MAC_EOL;\n" +
//                "                case 3:\n" +
//                "                    return UNIX_EOL;\n" +
//                "                case 2:\n" +
//                "                    return WINDOWS_EOL;\n" +
//                "                case 1:\n" +
//                "                    return SPACE;\n" +
//                "                case 0:\n" +
//                "                    return EOF;\n" +
                "                default:\n" +
                "                    throw new IllegalArgumentException(f(\"Token kind %i is unknown.\", kind));\n" +
                "            }\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";


        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(RAW)
                .setLexicalPreservationEnabled(true)
        );

        final ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        final CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);
        final ClassOrInterfaceDeclaration javaTokenCoid = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final EnumDeclaration kindEnum = javaTokenCoid
                .findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind"))
                .orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final MethodDeclaration valueOfMethodDeclaration = kindEnum.getMethodsByName("valueOf").get(0);
        final SwitchStmt valueOfSwitch = valueOfMethodDeclaration
                .findFirst(SwitchStmt.class)
                .orElseThrow(() -> new AssertionError("Can't find valueOf switch."));


        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        final SwitchEntry defaultEntry = valueOfSwitch.getDefaultSwitchEntry().get();
//        valueOfSwitch.getEntries().clear();
//        valueOfSwitch.getEntries().add(defaultEntry);
        valueOfSwitch.getEntries().removeIf(switchEntry -> switchEntry != defaultEntry);

//        "        EOF(0),\n" +
//                "        SPACE(1),\n" +
//                "        WINDOWS_EOL(2),\n" +
//                "        UNIX_EOL(3),\n" +
//                "        OLD_MAC_EOL(4),\n" +
//                "        SINGLE_LINE_COMMENT(5),\n" +
//                "        CTRL_Z(146);\n" +

        generateValueOfEntry(valueOfSwitch, "EOF", new IntegerLiteralExpr(0));
        generateValueOfEntry(valueOfSwitch, "SPACE", new IntegerLiteralExpr(1));
        generateValueOfEntry(valueOfSwitch, "WINDOWS_EOL", new IntegerLiteralExpr(2));
        generateValueOfEntry(valueOfSwitch, "UNIX_EOL", new IntegerLiteralExpr(3));
        generateValueOfEntry(valueOfSwitch, "OLD_MAC_EOL", new IntegerLiteralExpr(4));
        generateValueOfEntry(valueOfSwitch, "SINGLE_LINE_COMMENT", new IntegerLiteralExpr(5));
        generateValueOfEntry(valueOfSwitch, "CTRL_Z", new IntegerLiteralExpr(146));

//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(originalCode, LexicalPreservingPrinter.print(javaTokenCu));

    }


    @Test
    public void test() {
        String originalCode = "" +
                "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
                "\n" +
                "        EOF(0),\n" +
//                "        SPACE(1),\n" +
                "        CTRL_Z(146);\n" +
                "\n" +
                "        public static Kind valueOf(int kind) {\n" +
                "            switch(kind) {\n" +
//                "                case 1:\n" +
//                "                    return SPACE;\n" +
                "                case 0:\n" +
                "                    return EOF;\n" +
                "                default:\n" +
                "                    throw new IllegalArgumentException(f(\"Token kind %i is unknown.\", kind));\n" +
                "            }\n" +
                "        }\n" +
                "    }\n" +
                "}\n" +
                "";

        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(RAW)
                .setLexicalPreservationEnabled(true)
        );

        final ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        final CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);
        final ClassOrInterfaceDeclaration javaTokenCoid = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));

        ////
        final EnumDeclaration kindEnum = javaTokenCoid
                .findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind"))
                .orElseThrow(() -> new AssertionError("Can't find class in java file."));

        final MethodDeclaration valueOfMethodDeclaration = kindEnum.getMethodsByName("valueOf").get(0);
        final SwitchStmt switchStmt = valueOfMethodDeclaration
                .findFirst(SwitchStmt.class)
                .orElseThrow(() -> new AssertionError("Can't find valueOf switch."));

        ////
        NodeList<SwitchEntry> nodeList = switchStmt.getEntries();
        Node container = nodeList.getParentNodeForChildren();
        CsmElement element = ConcreteSyntaxModel.forClass(container.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel original = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, container);
        LexicalDifferenceCalculator.CalculatedSyntaxModel after = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListRemoval(element, ObservableProperty.ENTRIES, nodeList, 0);

        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(original, after);

        for (int i = 5; i < 15 && i < differenceElements.size(); i++) {
//        for (int i = 0; i < differenceElements.size(); i++) {
            DifferenceElement differenceElement = differenceElements.get(i);
//            if(differenceElement.isAdded() || differenceElement.isRemoved()) {
                System.out.println(i + " = " + differenceElement);
//            }
        }

        System.out.println();

        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        final SwitchEntry defaultEntry = switchStmt.getDefaultSwitchEntry().get();

        // OPTION #1: Remove all, then add one back in (temporarily has zero entries).
//        valueOfSwitch.getEntries().clear();
//        valueOfSwitch.getEntries().add(defaultEntry);

        // OPTION #2: Remove everything except the default (here we never end up with zero entries).
        switchStmt.getEntries().removeIf(switchEntry -> switchEntry != defaultEntry);


        generateValueOfEntry(switchStmt, "EOF", new IntegerLiteralExpr(0));
//        generateValueOfEntry(switchStmt, "SPACE", new IntegerLiteralExpr(1));
//        generateValueOfEntry(switchStmt, "WINDOWS_EOL", new IntegerLiteralExpr(2));
//        generateValueOfEntry(switchStmt, "UNIX_EOL", new IntegerLiteralExpr(3));
//        generateValueOfEntry(switchStmt, "OLD_MAC_EOL", new IntegerLiteralExpr(4));
//        generateValueOfEntry(switchStmt, "SINGLE_LINE_COMMENT", new IntegerLiteralExpr(5));
//        generateValueOfEntry(switchStmt, "CTRL_Z", new IntegerLiteralExpr(146));

//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(originalCode, LexicalPreservingPrinter.print(javaTokenCu));


    }


    private void generateValueOfEntry(SwitchStmt valueOfSwitch, String name, IntegerLiteralExpr kind) {
        final SwitchEntry entry = new SwitchEntry(new NodeList<>(kind), SwitchEntry.Type.STATEMENT_GROUP, new NodeList<>(new ReturnStmt(name)));

        // TODO: Why addFirst? Presumably to avoid adding after "default" (thus is effectively addBefore(default label).
        valueOfSwitch.getEntries().addFirst(entry);
    }
}
