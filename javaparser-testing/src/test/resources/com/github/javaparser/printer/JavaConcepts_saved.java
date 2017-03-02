package japa.bdd.samples;

import com.github.javaparser.JavaParser;
import japa.parser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Ignore;

import java.io.*;
import java.util.*;

@Ignore
@Deprecated
public class JavaConcepts<T extends List<int[]>, X> extends Base implements Serializable {

    static Class clz1 = String.class;

    protected Class clz2 = (String.class);

    Class clz3 = int.class;

    Class clz4 = (int.class);

    int[] arr = new int[10];

    byte bye = 0;

    byte byebye[] = null;

    short sh1, sh2 = 1;

    int intWithUnderscore = 1234_5678;

    long longWithUnderscore = 1234_5678L;

    float floatWithUnderscore = 1_234.5_678f;

    float floatWithUnderscoreAndExponent = 1_234e1_0f;

    double doubleWithUnderscore = 1_234.5_678;

    double doubleWithUnderscoreAndExponent = 1_234e1_0;

    int binaryLiteral = 0b101101;

    List<String>[][] arrLS = (List<String>[][]) new List<?>[10][];

    ;

    {
        int z = 0, y = 0;
        int a = (z) + y;
        a = (+z) + y;
        byte b = (byte) +y;
    }

    List<String> diamond1 = new LinkedList<>();

    @Deprecated()
    static class Ugly {

        static int x = 0;

        public static void main(String[] args) {
            x = +x;
            x = ~x;
            --x;
            boolean b = !false;
            x &= 2;
            x |= 2;
            x ^= 2;
            x -= 2;
            x %= 2;
            x /= 2;
            x *= 2;
            x <<= 2;
            x >>= 2;
            x >>>= 2;
            b = b || false;
            b = b | false;
            b = b & false;
            b = b ^ false;
            b = b != false;
            b = x > 1;
            b = x < 1;
            b = x >= 1;
            b = x <= 1;
            x = x << 1;
            x = x >> 1;
            x = x >>> 1;
            x = x - 1;
            x = x * 1;
            x = x % 1;
            x = x / 1;
        }
    }

    ;

    @Deprecated()
    int[][][][] arr2 = new int[10][2][1][0];

    volatile float fff = 0x1.fffeP+127f;

    char cc = 'a';

    int[][] arr3 = {{1, 2}, {3, 4}};

    static int[] arr4[] = {};

    public static JavaConcepts t;

    static {
        arr4 = new int[][]{{2}, {1}};
    }

    {
        arr3 = new int[][]{{2}, {1}};
    }

    public enum Teste {

        asc, def
    }

    public enum Sexo {

        m, @Deprecated
        f;

        public enum Sexo_ implements Serializable, Cloneable {
        }

        private Sexo() {
        }
    }

    @Deprecated
    public enum Enum {

        m(1) {
            @Override
            void mm() {
            }
        }, f(2) {
            void mm() {
            }
        };

        native void nnn();

        transient int x;

        private Enum(int x) {
            this.x = x;
        }

        abstract void mm();
    }

    strictfp double ddd() {
        return 0.0;
    }

    public <T, E> JavaConcepts(int x) {
        this.arr[0] = x;
        T val1 = null;
        E val2 = null;
        super.<T, E>check2(val1, val2);
        boolean b = true, y = false;
        abstract class X {

            int i = 0;

            public <D> X() {
            }

            public void m() {
            }
        }
        @Deprecated
        final class Y extends X {

            public Y() {
                super();
                JavaConcepts.this.cc = 'c';
                super.i = 1;
                Y.super.m();
            }

            public Y(int y) {
                super();
            }

            public Y(long x) {
                this();
            }
        }
    }

    public <T> JavaConcepts(String str) {
    }

    private class QWE extends JavaConcepts<List<int[]>, String> {

        @Deprecated
        final int z = 0;

        int i = (int) -1;

        public QWE(String... x) {
            <String>super(x[0]);
        }

        public QWE(int... x) {
            super(x[0]);
            i = x[0];
            assert true;
            assert 1 == 1 : 2;
            {
                int iii = 3;
                iii += 3;
            }
            label:
            {
                int iii = 1;
            }
            ;
            ;
            int min = -2147483648;
            long sl = 123123123123l;
            long minl = -9223372036854775808L;
            switch (i) {
            }
            ll:
            switch (i) {
                case 1:
                    System.out.println(1);
                    break ll;
                default: {
                    System.out.println("default");
                    break;
                }
                case 2:
                    if (t instanceof Base) {
                        System.out.println(1);
                    }
                    i++;
                    ++i;
            }
        }

        private synchronized int doSomething()[] {
            List<? extends Number> x = new ArrayList<Integer>();
            return new int[]{1};
        }
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
            xxx:
            while (x == 3) continue xxx;
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
                    A<Integer> a = new <String>A<Integer>(new Integer(11), "foo") {
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

class Base {

    public <A, B> void check2(A val1, B val2) {
    }
}

interface XXX extends Serializable, Cloneable {
}
