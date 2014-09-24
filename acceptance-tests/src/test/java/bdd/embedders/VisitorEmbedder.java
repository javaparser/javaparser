package bdd.embedders;

import bdd.steps.SharedSteps;
import bdd.steps.VisitorSteps;
import org.jbehave.core.steps.InjectableStepsFactory;
import org.jbehave.core.steps.InstanceStepsFactory;

import java.util.HashMap;
import java.util.Map;

/**
 * Class determines the step files and specific configuration for tests specifically related to vistor
 * implementations provided
 */
public class VisitorEmbedder extends BasicJapaEmbedder {

    @Override
    public InjectableStepsFactory stepsFactory() {
        Map<String, Object> state = new HashMap<String, Object>();
        return new InstanceStepsFactory(configuration(),
                new SharedSteps(state),
                new VisitorSteps(state));
    }
}
