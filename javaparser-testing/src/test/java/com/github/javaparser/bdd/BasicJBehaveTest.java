package com.github.javaparser.bdd;


import com.github.javaparser.bdd.steps.CommentParsingSteps;
import de.codecentric.jbehave.junit.monitoring.JUnitReportingRunner;
import org.jbehave.core.configuration.Configuration;
import org.jbehave.core.configuration.MostUsefulConfiguration;
import org.jbehave.core.failures.FailingUponPendingStep;
import org.jbehave.core.io.LoadFromClasspath;
import org.jbehave.core.io.StoryFinder;
import org.jbehave.core.junit.JUnitStories;
import org.jbehave.core.reporters.Format;
import org.jbehave.core.reporters.StoryReporterBuilder;
import org.jbehave.core.steps.InjectableStepsFactory;
import org.jbehave.core.steps.InstanceStepsFactory;

import java.util.List;

import static org.jbehave.core.io.CodeLocations.codeLocationFromClass;

abstract class BasicJBehaveTest extends JUnitStories {

    private final String storiesPath;

    public BasicJBehaveTest(String storiesPath) {
        this.storiesPath = storiesPath;
        JUnitReportingRunner.recommandedControls(configuredEmbedder());
    }

    @Override
    public final Configuration configuration() {
        return new MostUsefulConfiguration()
                // where to find the stories
                .useStoryLoader(new LoadFromClasspath(this.getClass()))
                        // Fails if Steps are not implemented
                .usePendingStepStrategy(new FailingUponPendingStep())
                        // CONSOLE and HTML reporting
                .useStoryReporterBuilder(new StoryReporterBuilder().withDefaultFormats()
                        .withFormats(Format.CONSOLE, Format.HTML));
    }

    @Override
    public final  List<String> storyPaths() {
        return new StoryFinder().findPaths(codeLocationFromClass(this.getClass()), storiesPath, "");
    }

}
