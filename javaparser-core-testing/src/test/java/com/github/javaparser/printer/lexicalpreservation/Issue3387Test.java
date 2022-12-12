package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.description.JavadocDescription;
import org.junit.jupiter.api.Test;

import java.util.StringJoiner;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue3387Test extends AbstractLexicalPreservingTest {

    @Test
    public void test3387() {
        considerCode(new StringJoiner("\n")
                .add("class A {")
                .add("")
                .add("\tpublic void setTheNumber(int number) {")
                .add("\t\tnumber = number;")
                .add("\t}")
                .add("")
                .add("}").toString());
        
        String expected = "class A {\n" + 
                "\n" + 
                "\t/**\n" + 
                "\t * Change Javadoc\n" + 
                "\t */\n" + 
                "\tpublic void setTheNumber(int number) {\n" + 
                "\t\tnumber = number;\n" + 
                "\t}\n" + 
                "\n" + 
                "}";

            MethodDeclaration md = cu.findFirst(MethodDeclaration.class).get();
            // create new javadoc comment
            Javadoc javadoc = new Javadoc(JavadocDescription.parseText("Change Javadoc"));
            md.setJavadocComment("\t", javadoc);
            System.out.println(LexicalPreservingPrinter.print(cu));
            assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }


}
