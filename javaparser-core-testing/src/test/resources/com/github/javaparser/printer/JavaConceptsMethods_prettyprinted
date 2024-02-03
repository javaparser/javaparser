/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package japa.bdd.samples;

import com.github.javaparser.JavaParser;
import japa.parser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import java.io.*;
import java.util.*;

public class JavaConceptsMethods {

    strictfp double ddd() {
        return 0.0;
    }

    public static void main(String[] args) throws ParseException, IOException {
        int x = 2;
        CompilationUnit cu = parse(new File("src/japa/parser/javacc/Parser.java"));
        System.out.println(cu);
        JavaConcepts teste = new JavaConcepts(2);
        JavaConcepts.QWE qwe = teste.new QWE(1);
        if (1 + 1 == 2) {
            teste = null;
            teste = new JavaConcepts(1);
        } else {
            x = 3;
            teste = new JavaConcepts(1);
            x = x == 0 ? 2 : 4;
        }
        if (true)
            x = 1;
        else
            x = 3;
        if (true)
            x = 1;
        else if (false)
            x = 3;
        else
            x = 2;
        while (true) {
            xxx: while (x == 3) continue xxx;
            break;
        }
        do {
            x++;
        } while (x < 100);
        do x++; while (x < 100);
        for (@Deprecated int i : arr4[0]) {
            x--;
        }
        for (@Deprecated final int i = 0, j = 1; i < 10; x++) {
            break;
        }
        int i, j;
        for (i = 0, j = 1; i < 10 && j < 2; i++, j--) {
            break;
        }
    }

    public static CompilationUnit parse(@Deprecated File file) throws ParseException, IOException {
        String a = ((String) "qwe");
        String x = ((String) clz1.getName());
        int y = ((Integer) (Object) x).intValue();
        synchronized (file) {
            file = null;
            file = new File("");
        }
        try {
            if (file == null) {
                throw new NullPointerException("blah");
            }
        } catch (final NullPointerException e) {
            System.out.println("catch");
        } catch (RuntimeException e) {
            System.out.println("catch");
        } finally {
            System.out.println("finally");
        }
        try {
            if (file == null) {
                throw new NullPointerException("blah");
            }
        } finally {
            System.out.println("finally");
        }
        try {
            if (file == null) {
                throw new NullPointerException("blah");
            }
        } catch (RuntimeException e) {
            System.out.println("catch");
        }
        try (InputStream in = createInputStream()) {
            System.out.println(in);
        } catch (IOException e) {
            System.out.println("catch");
        }
        try (InputStream in = createInputStream();
            InputStream in2 = createInputStream()) {
            System.out.println(in);
        } catch (IOException e) {
            System.out.println("catch");
        }
        try (InputStream in = createInputStream()) {
            System.out.println(in);
        }
        try {
            System.out.println("whatever");
        } catch (RuntimeException e) {
            System.out.println(e);
        } catch (final Exception | Error e) {
            System.out.println(e);
        }
        return JavaParser.parse(file);
    }

    class A<T extends Integer & Serializable> implements XXX, Serializable {

        public <ABC> A(Integer integer, ABC string) throws Exception, IOException {
        }
    }

    private <Y> void x(Map<? extends X, ? super T> x) {
        @Deprecated Comparator c = new Comparator() {

            public int compare(Object o1, Object o2) {
                try {
                    A<Integer> a = new <String> A<Integer>(new Integer(11), "foo") {
                    };
                } catch (Exception e) {
                }
                return 0;
            }

            @Override
            public boolean equals(Object obj) {
                return super.equals(obj);
            }
        };
    }

    private static InputStream createInputStream() {
        return new ByteArrayInputStream(null);
    }
}
