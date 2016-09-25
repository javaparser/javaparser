package com.github.javaparser.ast;

import com.github.javaparser.ast.body.VariableDeclaratorId;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;

public class MetaDataKeyTest {
    public static final MetaDataKey<String> ABC = new MetaDataKey<String>() {
    };
    public static final MetaDataKey<List<String>> LISTY = new MetaDataKey<List<String>>() {
    };
    public static final MetaDataKey<List<String>> DING = new MetaDataKey<List<String>>() {
    };

    @Test
    public void addAFewKeysAndSeeIfTheyAreStoredCorrectly() {
        Node node = new VariableDeclaratorId();

        node.setMetaData(ABC, "Hurray!");
        node.setMetaData(LISTY, Arrays.asList("a", "b"));
        node.setMetaData(ABC, "w00t");

        assertThat(node.getMetaData(ABC)).contains("w00t");
        assertThat(node.getMetaData(LISTY)).containsExactly("a", "b");
        assertThat(node.getMetaData(DING)).isNull();
    }

}
