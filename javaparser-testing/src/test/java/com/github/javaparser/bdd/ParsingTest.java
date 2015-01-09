package com.github.javaparser.bdd;

import com.github.javaparser.bdd.embedders.ParsingEmbedder;
import org.jbehave.core.embedder.Embedder;
import org.jbehave.core.io.StoryFinder;
import org.junit.Test;

import java.util.List;

import static org.jbehave.core.io.CodeLocations.codeLocationFromClass;

public class ParsingTest {

    @Test
    public void run() throws Throwable {
        Embedder embedder = new ParsingEmbedder();
        List<String> storyPaths = new StoryFinder().findPaths(codeLocationFromClass(this.getClass()), "**/bdd/parsing*.story", "");
        embedder.runStoriesAsPaths(storyPaths);
    }
}
