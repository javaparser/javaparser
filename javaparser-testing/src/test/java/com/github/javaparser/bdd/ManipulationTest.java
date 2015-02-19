package com.github.javaparser.bdd;

import com.github.javaparser.bdd.steps.ManipulationSteps;
import com.github.javaparser.bdd.steps.SharedSteps;
import de.codecentric.jbehave.junit.monitoring.JUnitReportingRunner;
import org.jbehave.core.steps.InjectableStepsFactory;
import org.jbehave.core.steps.InstanceStepsFactory;
import org.junit.runner.RunWith;

import java.util.HashMap;
import java.util.Map;

@RunWith(JUnitReportingRunner.class)
public class ManipulationTest extends BasicJBehaveTest {

    @Override
    public InjectableStepsFactory stepsFactory() {
        Map<String, Object> state = new HashMap<String, Object>();

        return new InstanceStepsFactory(configuration(),
                new SharedSteps(state),
                new ManipulationSteps(state));
    }

    public ManipulationTest() {
        super("**/bdd/manipulation*.story");
    }
}
