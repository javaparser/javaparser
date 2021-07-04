package org.openjml.runners;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.Ignore;
import org.junit.internal.AssumptionViolatedException;
import org.junit.internal.runners.model.EachTestNotifier;
import org.junit.runner.Description;
import org.junit.runner.Runner;
import org.junit.runner.notification.RunNotifier;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.Statement;
import org.junit.runners.BlockJUnit4ClassRunner;

/** This runner is a duplicate of org.junit.runners.Parameterized except that
 * tests whose assumptions are false are recorded as ignored rather than as a
 * success.
 */
// THIS IS HEAVILY COPIED FROM org.junit.runners.Parameterized, because the
// methods we need to override are final or private.

public class Ignorable extends org.junit.runners.Suite {

//    /**
//     * Annotation for a method which provides parameters to be injected into the
//     * test class constructor by <code>Parameterized</code>
//     */
//    @Retention(RetentionPolicy.RUNTIME)
//    @Target(ElementType.METHOD)
//    public static @interface Parameters {
//    }

//    private class TestClassRunnerForIgnorable extends
//            BlockJUnit4ClassRunner {
//
//    	TestClassRunnerForIgnorable(Class<?> type) throws InitializationError {
//            super(type);
//        }
//
//        
//        @Override
//        protected void runChild(final FrameworkMethod method, RunNotifier notifier) {
//            Description description= describeChild(method);
//            if (method.getAnnotation(Ignore.class) != null) {
//                notifier.fireTestIgnored(description);
//            } else {
//                //runLeaf(methodBlock(method), description, notifier);
//                Statement statement = methodBlock(method);
//                EachTestNotifier eachNotifier= new EachTestNotifier(notifier, description);
//                eachNotifier.fireTestStarted();
//                try {
//                    statement.evaluate();
//                } catch (AssumptionViolatedException e) {
//                    eachNotifier.fireTestIgnored();
//                } catch (Throwable e) {
//                    eachNotifier.addFailure(e);
//                } finally {
//                    eachNotifier.fireTestFinished();
//                }
//            }
//        }
//
//    }

    private final ArrayList<Runner> runners= new ArrayList<Runner>();
    {
    	runners.clear();
    }
    /**
     * Only called reflectively. Do not use programmatically.
     */
    public Ignorable(Class<?> klass) throws Throwable {
        super(klass, Collections.<Runner>emptyList());
    	runners.add(new BlockJUnit4ClassRunner(getTestClass().getJavaClass()) {
            @Override
            protected void runChild(final FrameworkMethod method, RunNotifier notifier) {
                Description description= describeChild(method);
                if (method.getAnnotation(Ignore.class) != null) {
                    notifier.fireTestIgnored(description);
                } else {
                    //runLeaf(methodBlock(method), description, notifier);
                    Statement statement = methodBlock(method);
                    EachTestNotifier eachNotifier= new EachTestNotifier(notifier, description);
                    eachNotifier.fireTestStarted();
                    try {
                        statement.evaluate();
                    } catch (AssumptionViolatedException e) {
                        eachNotifier.fireTestIgnored();
                    } catch (Throwable e) {
                        eachNotifier.addFailure(e);
                    } finally {
                        eachNotifier.fireTestFinished();
                    }
                }
            }
    	});
    }

    
}
