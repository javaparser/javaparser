package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CalculatedSyntaxModel;
import com.github.javaparser.utils.Log;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class LexicalPreservationWithTokenKindGeneratorTest {

    static {
        Log.setAdapter(new Log.StandardOutStandardErrorAdapter());
    }

    @Test
    public void removeLastEnumConstant() {
        final String originalCode = "" +
                "    public enum Kind {\n" +
                "\n" +
                "      CTRL_Z(146);\n" +
                "\n" +
                "        private final int kind;\n" +
                "\n" +
                "    }\n" +
                "";


        final String expectedOutput_lexical = "" +
                "    public enum Kind {\n" +
                "\n" +
                "        \n" +
//                "        ;\n" +
//                "        CTRL_Z(146);\n" +
//                "\n" +
                "        private final int kind;\n" +
                "\n" +
                "    }\n" +
                "";


        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(RAW)
                .setLexicalPreservationEnabled(true)
        );

        ////
        final ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        final CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);
//        final ClassOrInterfaceDeclaration javaTokenCoid = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));

        ////
        final EnumDeclaration kindEnum = javaTokenCu
                .findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind"))
                .orElseThrow(() -> new AssertionError("Can't find class in java file."));

        // Reset the enum:
        kindEnum.getEntries().clear();

//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(expectedOutput_lexical, LexicalPreservingPrinter.print(javaTokenCu));

    }


    @Test
    public void foo_enumOnly() {
        final String originalCode = "" +
                "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
                "\n" +
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
                "    }\n" +
                "\n" +
                "}\n" +
                "";


        final String expectedOutput_lexical = "public class JavaToken {\n" +
                "\n" +
                "    public enum Kind {\n" +
                "        \n" +
                "        EOF(0),\n" +
                "        SPACE(1),\n" +
                "        WINDOWS_EOL(2),\n" +
                "        UNIX_EOL(3),\n" +
                "        OLD_MAC_EOL(4),\n" +
                "        SINGLE_LINE_COMMENT(5),\n" +
                "        CTRL_Z(146);\n" +
                "\n" +
                "\n" +
                "        private final int kind;\n" +
                "\n" +
                "    }\n" +
                "\n" +
                "}\n" +
                "";

        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLanguageLevel(RAW)
                .setLexicalPreservationEnabled(true)
        );

        ////
        final ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        final CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);
        final ClassOrInterfaceDeclaration javaTokenCoid = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));

        ////
        final EnumDeclaration kindEnum = javaTokenCoid
                .findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind"))
                .orElseThrow(() -> new AssertionError("Can't find class in java file."));

        // Reset the enum:
        kindEnum.getEntries().clear();

        generateEnumEntry(kindEnum, "EOF", new IntegerLiteralExpr(0));
//        generateEnumEntry(kindEnum, "SPACE", new IntegerLiteralExpr(1));
//        generateEnumEntry(kindEnum, "WINDOWS_EOL", new IntegerLiteralExpr(2));
//        generateEnumEntry(kindEnum, "UNIX_EOL", new IntegerLiteralExpr(3));
//        generateEnumEntry(kindEnum, "OLD_MAC_EOL", new IntegerLiteralExpr(4));
//        generateEnumEntry(kindEnum, "SINGLE_LINE_COMMENT", new IntegerLiteralExpr(5));
//        generateEnumEntry(kindEnum, "CTRL_Z", new IntegerLiteralExpr(146));

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

        generateValueOfEntry_toStart(valueOfSwitch, "EOF", new IntegerLiteralExpr(0));
        generateValueOfEntry_toStart(valueOfSwitch, "SPACE", new IntegerLiteralExpr(1));
        generateValueOfEntry_toStart(valueOfSwitch, "WINDOWS_EOL", new IntegerLiteralExpr(2));
        generateValueOfEntry_toStart(valueOfSwitch, "UNIX_EOL", new IntegerLiteralExpr(3));
        generateValueOfEntry_toStart(valueOfSwitch, "OLD_MAC_EOL", new IntegerLiteralExpr(4));
        generateValueOfEntry_toStart(valueOfSwitch, "SINGLE_LINE_COMMENT", new IntegerLiteralExpr(5));
        generateValueOfEntry_toStart(valueOfSwitch, "CTRL_Z", new IntegerLiteralExpr(146));

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
//                "        EOF(0),\n" +
////                "        SPACE(1),\n" +
//                "        CTRL_Z(146);\n" +
                "        ;\n" + // Deliberately omit these for now in this test...
                "\n" +
                "        public Kind valueOf(int kind) {\n" +
                "            switch(kind) {\n" +
                "                \n" +
                "                \n" +
                "                case 1:\n" +
                "                    return SPACE;\n" +
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
        CsmElement element = ConcreteSyntaxModel.forClass(nodeList.getParentNodeForChildren().getClass());

        CalculatedSyntaxModel original = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, nodeList.getParentNodeForChildren());
        CalculatedSyntaxModel afterRemovingOne = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListRemoval(element, ObservableProperty.ENTRIES, nodeList, 0);

//        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(original, afterRemovingOne);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculateImpl(original, afterRemovingOne);
        System.out.println();
        System.out.println("==BEFORE ELEMENTS==");
        for (int i = 0; i < original.elements.size(); i++) {
            CsmElement originalElement = original.elements.get(i);
            System.out.println(i + " = " + escapeNewlines(originalElement.toString()));
        }
//        System.out.println();
//        System.out.println("==AFTER REMOVING ONE==");
//        for (int i = 0; i < afterRemovingOne.elements.size(); i++) {
//            CsmElement afterElement = afterRemovingOne.elements.get(i);
//            System.out.println(i + " = " + escapeNewlines(afterElement.toString()));
//        }
//        System.out.println();
//        System.out.println();
//        for (int i = 0; i < differenceElements.size(); i++) {
//            DifferenceElement differenceElement = differenceElements.get(i);
//            if (differenceElement.isAdded()) {
//                System.out.println("(++) " + i + " = " + escapeNewlines(differenceElement.toString()));
//            } else if (differenceElement.isRemoved()) {
//                System.out.println("(--) " + i + " = " + escapeNewlines(differenceElement.toString()));
//            } else {
//                System.out.println(i + " = " + escapeNewlines(differenceElement.toString()));
//            }
//        }
//
//        System.out.println();
//        System.out.println();

        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        final SwitchEntry defaultEntry = switchStmt.getDefaultSwitchEntry().get();

        // OPTION #1: Remove all, then add one back in (temporarily has zero entries).
//        valueOfSwitch.getEntries().clear();
//        valueOfSwitch.getEntries().add(defaultEntry);

        // OPTION #2: Remove everything except the default (here we never end up with zero entries).
        switchStmt.getEntries().removeIf(switchEntry -> switchEntry != defaultEntry);


//        System.out.println();
//        System.out.println("==NODETEXT==");
//        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(switchStmt);
//        for (int i = 0; i < nodeText.getElements().size(); i++) {
//            TextElement nodeTextElement = nodeText.getElements().get(i);
//            System.out.println(i + " = " + escapeNewlines(nodeTextElement.toString()));
//        }

        generateValueOfEntry_toStart(switchStmt, "EOF", new IntegerLiteralExpr(0));
        generateValueOfEntry_toStart(switchStmt, "SPACE", new IntegerLiteralExpr(1));
//        generateValueOfEntry(switchStmt, "WINDOWS_EOL", new IntegerLiteralExpr(2));
//        generateValueOfEntry(switchStmt, "UNIX_EOL", new IntegerLiteralExpr(3));
//        generateValueOfEntry(switchStmt, "OLD_MAC_EOL", new IntegerLiteralExpr(4));
//        generateValueOfEntry(switchStmt, "SINGLE_LINE_COMMENT", new IntegerLiteralExpr(5));
//        generateValueOfEntry(switchStmt, "CTRL_Z", new IntegerLiteralExpr(146));

        CalculatedSyntaxModel original2 = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, nodeList.getParentNodeForChildren());
        System.out.println();
        System.out.println("==BEFORE ELEMENTS==");
        for (int i = 0; i < original2.elements.size(); i++) {
            CsmElement originalElement = original2.elements.get(i);
            System.out.println(i + " = " + escapeNewlines(originalElement.toString()));
        }

//        printDifferences(original, afterRemovingOne);
        printDifferences(original, original);

        System.out.println();
        System.out.println();

        Node parentNodeForChildren = nodeList.getParentNodeForChildren();
        System.out.println("parentNodeForChildren = " + parentNodeForChildren);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(parentNodeForChildren);

        System.out.println("indentation (" + indentation.size() + ") = " + indentation);
//        indentation.forEach(System.out::println);

//        assertEquals(originalCode, javaTokenCu.toString());
        assertEqualsStringIgnoringEol(originalCode, LexicalPreservingPrinter.print(javaTokenCu));


    }

    @Test
    public void test3() {
        String originalCode = "" +
                "class JavaToken {Kind valueOf(int kind) {\n" +
                "        switch(kind) {\n" +
//                "            \n" +
//                "            \n" +
//                "            \n" +
                "        }\n" +
                "}\n" +
                "}\n" +
                "";

        String expected_lexical = "" +
                "class JavaToken {Kind valueOf(int kind) {\n" +
                "        switch(kind) {\n" +
                "            case 1:\n" +
                "                return SPACE;\n" +
                "            case 0:\n" +
                "                return EOF;\n" +
//                "            \n" +
//                "            \n" +
//                "            \n" +
                "        }\n" +
                "}\n" +
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
        final MethodDeclaration valueOfMethodDeclaration = javaTokenCoid.getMethodsByName("valueOf").get(0);
        final SwitchStmt switchStmt = valueOfMethodDeclaration
                .findFirst(SwitchStmt.class)
                .orElseThrow(() -> new AssertionError("Can't find valueOf switch."));

        ////
        NodeList<SwitchEntry> nodeList = switchStmt.getEntries();
        CsmElement element = ConcreteSyntaxModel.forClass(nodeList.getParentNodeForChildren().getClass());


        CalculatedSyntaxModel original = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, nodeList.getParentNodeForChildren());


        generateValueOfEntry(switchStmt, "EOF", new IntegerLiteralExpr(0));
        generateValueOfEntry(switchStmt, "SPACE", new IntegerLiteralExpr(1));
//        generateValueOfEntry(switchStmt, "WINDOWS_EOL", new IntegerLiteralExpr(2));
//        generateValueOfEntry(switchStmt, "UNIX_EOL", new IntegerLiteralExpr(3));
//        generateValueOfEntry(switchStmt, "OLD_MAC_EOL", new IntegerLiteralExpr(4));
//        generateValueOfEntry(switchStmt, "SINGLE_LINE_COMMENT", new IntegerLiteralExpr(5));
//        generateValueOfEntry(switchStmt, "CTRL_Z", new IntegerLiteralExpr(146));


        CalculatedSyntaxModel after = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, nodeList.getParentNodeForChildren());

        printDifferences(original, after);
        assertEqualsStringIgnoringEol(expected_lexical, LexicalPreservingPrinter.print(javaTokenCu));

    }


    public void printDifferences(CalculatedSyntaxModel before, CalculatedSyntaxModel after) {
        System.out.println();
        System.out.println();
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculateImpl(before, after);
        for (int i = 0; i < differenceElements.size(); i++) {
            DifferenceElement differenceElement = differenceElements.get(i);
            if (differenceElement.isAdded()) {
                System.out.println("(++) " + i + " = " + escapeNewlines(differenceElement.toString()));
            } else if (differenceElement.isRemoved()) {
                System.out.println("(--) " + i + " = " + escapeNewlines(differenceElement.toString()));
            } else {
                System.out.println(i + " = " + escapeNewlines(differenceElement.toString()));
            }
        }
    }

    public String escapeNewlines(String string) {
//        return string.replace("\r", "\\r").replace("\n", "\\n");
        return string.replace("; ", ";\n    - ");
    }

    private void generateValueOfEntry(SwitchStmt valueOfSwitch, String name, IntegerLiteralExpr kind) {
        // HELPER METHOD -- single place to toggle adding to start or end
        generateValueOfEntry_toStart(valueOfSwitch, name, kind);
//        generateValueOfEntry_toEnd(valueOfSwitch, name, kind);
    }

    private void generateValueOfEntry_toStart(SwitchStmt valueOfSwitch, String name, IntegerLiteralExpr kind) {
        final SwitchEntry entry = new SwitchEntry(new NodeList<>(kind), SwitchEntry.Type.STATEMENT_GROUP, new NodeList<>(new ReturnStmt(name)));
        valueOfSwitch.getEntries().addFirst(entry);
    }

    private void generateValueOfEntry_toEnd(SwitchStmt valueOfSwitch, String name, IntegerLiteralExpr kind) {
        final SwitchEntry entry = new SwitchEntry(new NodeList<>(kind), SwitchEntry.Type.STATEMENT_GROUP, new NodeList<>(new ReturnStmt(name)));
        valueOfSwitch.getEntries().add(entry);
    }

    private void generateEnumEntry(EnumDeclaration kindEnum, String name, IntegerLiteralExpr kind) {
        final EnumConstantDeclaration enumEntry = new EnumConstantDeclaration(name);
        enumEntry.getArguments().add(kind);
        kindEnum.addEntry(enumEntry);
    }
}
