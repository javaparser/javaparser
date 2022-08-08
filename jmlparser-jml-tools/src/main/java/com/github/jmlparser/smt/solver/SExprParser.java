package com.github.jmlparser.smt.solver;

import com.github.jmlparser.smt.model.SAtom;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SList;
import org.jetbrains.annotations.Nullable;

import java.io.*;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import static java.lang.String.format;

public class SExprParser {
    public static SExpr parse(String input) throws IOException {
        return parse(new StringReader(input));
    }

    public static SExpr parse(Reader reader) throws IOException {
        return parse(new PushbackReader(reader));
    }

    @Nullable
    public static SExpr parse(PushbackReader reader) throws IOException {
        int c = peekChar(reader);
        if (c == (char) -1) // end of input
            return null;
        else if (c == '(') {
            consumeChar(reader); // consume '('
            ArrayList<SExpr> seq = new ArrayList<>();
            do {
                c = peekChar(reader);
                if (c == ')') {
                    consumeChar(reader);
                    break;
                }
                SExpr child = parse(reader);
                if (child == null) {
                    throw new IllegalArgumentException("List not closed.");
                }
                seq.add(child);
            } while (true);
            return new SList(null, null, seq.toArray(new SExpr[0]));
        } else if (Character.isDigit(c) || c == '-') {
            return parseNumber(reader);
        } else if (Character.isAlphabetic(c) || c == ':') {
            return parseSymbol(reader);
        } else if (c == '"') {
            return parseString(reader);
        } else {
        }
        throw new IllegalStateException(format("Unexpected character: %c (%d)", c, c));
    }

    private static SExpr parseString(PushbackReader reader) throws IOException {
        StringBuilder symbol = new StringBuilder("\"");
        consumeChar(reader);
        int c;
        do {
            c = reader.read();
            if (c == -1)
                throw new RuntimeException("String literal early aborted");
            symbol.append((char) c);
        } while (c != '"');
        return new SAtom(null, null, symbol.toString());
    }

    private static int consumeChar(PushbackReader reader) throws IOException {
        return reader.read();
    }

    private static int peekChar(PushbackReader reader) throws IOException {
        consumeEmptiness(reader);
        int c = reader.read();
        reader.unread(c);
        return c;
    }

    private static void consumeEmptiness(PushbackReader reader) throws IOException {
        int c;
        do {
            consumeWhitespace(reader);
            consumeComment(reader);
            c = reader.read();
            reader.unread(c);
        } while (Character.isWhitespace(c) || c == ';');
    }

    private static void consumeWhitespace(PushbackReader reader) throws IOException {
        consumeUntil(reader, (x) -> !Character.isWhitespace(x));
    }

    private static void consumeComment(PushbackReader reader) throws IOException {
        int c = reader.read();
        if (c == ';') {
            consumeUntil(reader, (x) -> x != '\n');
        } else {
            reader.unread(c);
        }
    }

    private static int consumeUntil(PushbackReader reader, Predicate<Integer> pred) throws IOException {
        int c;
        do {
            c = reader.read();
        } while (!pred.test(c) && c != (char) -1);
        reader.unread(c);
        return c;
    }

    private static SExpr parseNumber(PushbackReader reader) throws IOException {
        int num = 0;
        int factor = 1;
        int c = reader.read();
        if (c == '-') {
            factor = -1;
        } else {
            reader.unread(c);
        }

        do {
            c = reader.read();
            if (c == -1) break;
            if (c == ')' || Character.isWhitespace(c) || c == ':') {
                reader.unread(c);
                break;
            }
            if (Character.isDigit(c)) {
                num = (num * 10) + (c - '0');
            } else {
                throw new IllegalStateException("Given number is invalid. Char " + (char) c + " found");
            }
        } while (true);
        return new SAtom(null, null, "" + (num * factor));
    }

    private static SExpr parseSymbol(PushbackReader reader) throws IOException {
        StringBuilder symbol = new StringBuilder();
        do {
            int c = reader.read();
            if (c == -1) break;
            if (c == ')' || Character.isWhitespace(c)) {
                reader.unread(c);
                break;
            }
            symbol.append((char) c);
        } while (true);
        return new SAtom(null, null, symbol.toString());
    }

    public static List<SExpr> parseAll(Reader in) throws IOException {
        PushbackReader r = new PushbackReader(in);
        List<SExpr> exprs = new ArrayList<>(1024);
        int c;
        while ((c = r.read()) != -1) {
            r.unread(c);
            SExpr sexpr = SExprParser.parse(r);
            if (sexpr == null) break;
            exprs.add(sexpr);
        }
        return exprs;
    }
}
