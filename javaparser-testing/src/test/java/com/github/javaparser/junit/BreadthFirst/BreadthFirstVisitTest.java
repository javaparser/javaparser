package com.github.javaparser.junit.BreadthFirst;

import com.github.javaparser.junit.wiki_samples.TestFileToken;
import org.junit.Test;

public class BreadthFirstVisitTest {
	@Test
	public void testCode() throws Exception {
		try (TestFileToken f = new TestFileToken("forGitHubTest.java")) {
			GitHubTest.main();
		}
	}

}
