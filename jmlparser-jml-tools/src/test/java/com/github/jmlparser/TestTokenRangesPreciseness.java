package com.github.jmlparser;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.jml.NodeWithJmlTags;
import com.github.javaparser.jml.JmlUtility;
import com.google.common.truth.Truth;
import org.assertj.core.util.Streams;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (18.10.22)
 */
class TestTokenRangesPreciseness extends TestWithJavaParser {

    @Test
    void lineColumnIndex() {
        var lci = new LineColumnIndex("""
                Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam
                nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua.
                    At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea
                  takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet,
                   consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore
                 et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo 
                  duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est 
                Lorem ipsum dolor sit amet.
                """);


        Truth.assertThat(lci.substring(1, 1, 1, 5))
                .isEqualTo("Lorem");

        Truth.assertThat(lci.substring(2, 1, 2, 6))
                .isEqualTo("nonumy");

        Truth.assertThat(lci.substring(6, 18, 6, 25))
                .isEqualTo("aliquyam");
    }

    @TestFactory
    Stream<DynamicTest> ihm() throws Throwable {
        final var content =
                Files.readString(
                        Paths.get(
                                getClass().getResource("/ihm/VerifiedIdentityHashMap.java").getPath()));
        var result = parser.parse(content);
        Assertions.assertTrue(result.isSuccessful());
        return testTokenRanges(result.getResult().get(), content);
    }


    @TestFactory
    Stream<DynamicTest> test() throws Throwable {
        final var content =
                Files.readString(
                        Paths.get(
                                getClass().getResource("/com/github/jmlparser/TokenTest.java").getPath()));
        var result = parser.parse(content);
        Assertions.assertTrue(result.isSuccessful());
        return testTokenRanges(result.getResult().get(), content);
    }

    private Stream<DynamicTest> testTokenRanges(CompilationUnit node, String content) {
        var lci = new LineColumnIndex(content);
        return JmlUtility.getAllNodes(node)
                .filter(it -> it instanceof NodeWithJmlTags<?>)
                .flatMap(it -> checkTokenRange(lci, it));
        //checkTokenRange(lci, node);
    }

    private Stream<DynamicTest> checkTokenRange(LineColumnIndex lci, Node it) {
        var tr = it.getTokenRange();
        return tr.map(javaTokens -> checkTokenRange(lci, javaTokens)).orElse(Stream.empty());
    }

    private Stream<DynamicTest> checkTokenRange(LineColumnIndex lci, TokenRange javaTokens) {
        return Streams.stream(javaTokens)
                .filter(it -> it.getKind() != GeneratedJavaParserConstants.EOF)
                .map(javaToken -> DynamicTest.dynamicTest(javaToken.toString(), () -> {
                    final var substring = lci.substring(javaToken.getRange().get());
                    final var text = javaToken.getText();
                    if (!(substring.equals("@") && text.equals(" "))) {
                        Truth.assertThat(substring).isEqualTo(text);
                    }
                }));
    }
}
