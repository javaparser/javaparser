package com.github.javaparser.ast.comments;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Paths;

import static org.junit.Assert.*;

/**
 * Created by Kido on 9/24/16.
 */
public class JavadocCommentTest {

    @Test
    public void testGetText() throws Exception {
        Visitor v = new Visitor();
        try {
            FileInputStream fis = new FileInputStream("temp/Test1.java");
            CompilationUnit cu = JavaParser.parse(fis);
            fis.close();
            v.visit(cu, null);
            String doc = v.doc;
            String output = "This is a simple Java Doc.\nThe output should be without stars.";
            assertTrue(doc.length() == output.length());
            assertTrue(output.equals(doc));
        } catch (IOException e) {
            System.out.println("cannot open file.");
        }
    }


    private class Visitor extends VoidVisitorAdapter{

        String doc;
        @Override
        public void visit(JavadocComment n, Object arg) {
            doc = n.getText();
            super.visit(n, arg);
        }
    }

}