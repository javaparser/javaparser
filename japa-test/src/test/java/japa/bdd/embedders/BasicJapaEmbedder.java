package japa.bdd.embedders;

import org.jbehave.core.configuration.Configuration;
import org.jbehave.core.configuration.MostUsefulConfiguration;
import org.jbehave.core.embedder.Embedder;
import org.jbehave.core.embedder.EmbedderControls;
import org.jbehave.core.failures.FailingUponPendingStep;
import org.jbehave.core.io.LoadFromClasspath;
import org.jbehave.core.reporters.Format;
import org.jbehave.core.reporters.StoryReporterBuilder;


/**
 * Class provides basic configuration for other embedders to reuse
 */
public abstract class BasicJapaEmbedder extends Embedder {

    @Override
    public EmbedderControls embedderControls() {
        return new EmbedderControls().doIgnoreFailureInStories(false).doIgnoreFailureInView(false);
    }

    @Override
    public Configuration configuration() {
        return new MostUsefulConfiguration()
                // where to find the stories
                .useStoryLoader(new LoadFromClasspath(this.getClass()))
                        // Fails if Steps are not implemented
                .usePendingStepStrategy(new FailingUponPendingStep())
                        // CONSOLE and HTML reporting
                .useStoryReporterBuilder(new StoryReporterBuilder().withDefaultFormats()
                        .withFormats(Format.CONSOLE, Format.HTML));
    }
}
