package com.github.javaparser.ast;

import com.github.javaparser.ast.body.VariableDeclaratorId;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;

public class UserDataKeyTest {
    public static final UserDataKey<String> ABC = new UserDataKey<String>() {
    };
    public static final UserDataKey<List<String>> LISTY = new UserDataKey<List<String>>() {
    };
    public static final UserDataKey<List<String>> DING = new UserDataKey<List<String>>() {
    };

    @Test
    public void addAFewKeysAndSeeIfTheyAreStoredCorrectly() {
        Node node = new VariableDeclaratorId();

        node.setUserData(ABC, "Hurray!");
        node.setUserData(LISTY, Arrays.asList("a", "b"));
        node.setUserData(ABC, "w00t");

        assertThat(node.getUserData(ABC)).contains("w00t");
        assertThat(node.getUserData(LISTY)).containsExactly("a", "b");
        assertThat(node.getUserData(DING)).isNull();
    }

}
