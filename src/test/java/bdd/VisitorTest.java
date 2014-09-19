package bdd;

import bdd.embedders.VisitorEmbedder;
import org.jbehave.core.embedder.Embedder;
import org.jbehave.core.io.StoryFinder;
import org.junit.Test;

import java.util.List;

import static org.jbehave.core.io.CodeLocations.codeLocationFromClass;

public class VisitorTest {

    @Test
    public void run() throws Throwable {
        Embedder embedder = new VisitorEmbedder();
        List<String> storyPaths = new StoryFinder().findPaths(codeLocationFromClass(this.getClass()), "**/bdd/visitor*.story", "");
        embedder.runStoriesAsPaths(storyPaths);
    }
}
