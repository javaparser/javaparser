package com.github.javaparser.ast;

import com.github.javaparser.ast.expr.SimpleName;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;

public class DataKeyTest {
    public static final DataKey<String> ABC = new DataKey<String>() {
    };
    public static final DataKey<List<String>> LISTY = new DataKey<List<String>>() {
    };
    public static final DataKey<List<String>> DING = new DataKey<List<String>>() {
    };

    @Test
    public void addAFewKeysAndSeeIfTheyAreStoredCorrectly() {
        Node node = new SimpleName();

        node.setData(ABC, "Hurray!");
        node.setData(LISTY, Arrays.asList("a", "b"));
        node.setData(ABC, "w00t");

        assertThat(node.getData(ABC)).contains("w00t");
        assertThat(node.getData(LISTY)).containsExactly("a", "b");
        assertThat(node.getData(DING)).isNull();
    }

}
