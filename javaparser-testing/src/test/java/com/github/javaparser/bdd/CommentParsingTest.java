package com.github.javaparser.bdd;

import com.github.javaparser.bdd.steps.CommentParsingSteps;
import de.codecentric.jbehave.junit.monitoring.JUnitReportingRunner;
import org.jbehave.core.steps.InjectableStepsFactory;
import org.jbehave.core.steps.InstanceStepsFactory;
import org.junit.runner.RunWith;

@RunWith(JUnitReportingRunner.class)
public class CommentParsingTest extends BasicJBehaveTest {

    @Override
    public InjectableStepsFactory stepsFactory() {
        return new InstanceStepsFactory(configuration(), new CommentParsingSteps());
    }

    public CommentParsingTest() {
        super("**/bdd/comment*.story");
    }
}

