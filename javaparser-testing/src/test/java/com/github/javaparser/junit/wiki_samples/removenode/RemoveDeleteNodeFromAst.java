package com.github.javaparser.junit.wiki_samples.removenode;

import com.github.javaparser.junit.wiki_samples.TestFileToken;
import org.junit.Test;

public class RemoveDeleteNodeFromAst {
    @Test
    public void testCode1() throws Exception {
        try (TestFileToken f = new TestFileToken("forGitHubTest.java")) {
            GitHubTest.main();
        }
    }

    @Test
    public void testCode2() throws Exception {
        try (TestFileToken f = new TestFileToken("forGitHubTest.java")) {
            GitHubTest_2.main();
        }
    }
}
