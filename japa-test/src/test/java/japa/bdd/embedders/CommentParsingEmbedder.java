package japa.bdd.embedders;

import japa.bdd.steps.CommentParsingSteps;
import org.jbehave.core.steps.InjectableStepsFactory;
import org.jbehave.core.steps.InstanceStepsFactory;

/**
 * Class determines the step files and specific configuration for tests related to the comments parser
 */
public class CommentParsingEmbedder extends BasicJapaEmbedder {

    @Override
    public InjectableStepsFactory stepsFactory() {
        return new InstanceStepsFactory(configuration(), new CommentParsingSteps());
    }
}
