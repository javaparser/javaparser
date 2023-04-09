package com.github.jmlparser.mlpp;

import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaToken;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;
import com.github.jmlparser.utils.Helper;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (07.04.23)
 */
public class FeatureExtractor {
    private final JavaParser parser;
    private final PrintWriter out = new PrintWriter("features.csv");

    public FeatureExtractor() throws FileNotFoundException {
        ParserConfiguration config = new ParserConfiguration();
        config.setProcessJml(true);
        parser = new JavaParser(config);
    }

    public void extract(Path path) throws IOException {
        var cu = parser.parse(path);
        if (cu.isSuccessful()) {
            var nodes = Helper.findAllJmlContainers(cu.getResult().get());
            extractN(nodes);
        }
    }

    private void extractN(List<Node> nodes) {
        for (Node node : nodes) {
            final var tokenRange = node.getTokenRange();
            tokenRange.ifPresent(javaTokens -> extract(javaTokens.getBegin(), javaTokens.getEnd()));
        }
    }

    private void extract(JavaToken begin, JavaToken end) {
        var cur = begin;
        var seq = new ArrayList<JavaToken>(1024);
        while (cur != null && cur != end) {
            if (!cur.getCategory().isWhitespaceOrComment()) {
                seq.add(cur);
            }
            cur = cur.getNextToken().orElse(null);
        }
        extract(seq);
    }

    private void extract(List<JavaToken> seq) {
        var iter = new FillNull(seq.iterator());
        JavaToken prev2 = null, prev1 = null, cur = iter.next(), next = iter.next();
        while (cur != null) {
            var tokenid0 = getKind(cur);
            var tokenid1 = getKind(prev1);
            var tokenid2 = getKind(prev2);
            var tokenidn = getKind(next);

            var widthleft = 120 - cur.getRange().get().end.column;

            var lineident = 0;

            var followed_by_newline = next != null && cur.getRange().get().end.line != next.getRange().get().begin.line;
            var followed_by_indent = next != null ? next.getRange().get().begin.column : 0;


            out.format("%d\t%d\t%d\t%d\t%d\t%d\t%s\t%d\n",
                    tokenid0, tokenid1, tokenid2, tokenidn, widthleft, lineident, followed_by_newline, followed_by_indent
            );

            prev2 = prev1;
            prev1 = cur;
            cur = next;
            next = next == null ? null : iter.next();
        }

    }

    private int getCurrentLineIndent() {
        return 0;
    }

    private static int getKind(JavaToken cur) {
        if (cur == null) return -1;
        return cur.getKind();
    }

    public static void main(String[] args) throws IOException {
        var e = new FeatureExtractor();
        e.printHead();
        for (String arg : args) {
            Files.walk(Paths.get(arg)).forEach(it -> {
                try {
                    e.extract(it);
                } catch (IOException ex) {
                    ex.printStackTrace();
                }
            });
        }
        e.out.flush();
    }

    private void printHead() {
        out.format("tokenid0\ttokenid1\ttokenid2\ttokenidn\twidthleft\tlineident\tfollowed_by_newline\tfollowed_by_indent\n");
    }

    private static class FillNull implements Iterator<JavaToken> {
        private final Iterator<JavaToken> iter;

        public FillNull(Iterator<JavaToken> iterator) {
            this.iter = iterator;
        }

        @Override
        public boolean hasNext() {
            return iter.hasNext();
        }

        @Override
        public JavaToken next() {
            if (iter.hasNext())
                return iter.next();
            return null;
        }
    }
}
