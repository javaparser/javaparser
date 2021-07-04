package org.openjml.runners;

import java.lang.annotation.Annotation;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.Ignore;
import org.junit.internal.AssumptionViolatedException;
import org.junit.internal.runners.model.EachTestNotifier;
import org.junit.runner.Description;
import org.junit.runner.Runner;
import org.junit.runner.notification.RunNotifier;
import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.Statement;
import org.junit.runners.model.TestClass;

/** This runner is a duplicate of org.junit.runners.Parameterized except that
 * tests whose assumptions are false are recorded as ignored rather than as a
 * success.
 */
// THIS IS HEAVILY COPIED FROM org.junit.runners.Parameterized, because the
// methods we need to override are final or private.

public class ParameterizedIgnorable extends org.junit.runners.Suite {

//    /**
//     * Annotation for a method which provides parameters to be injected into the
//     * test class constructor by <code>Parameterized</code>
//     */
//    @Retention(RetentionPolicy.RUNTIME)
//    @Target(ElementType.METHOD)
//    public static @interface Parameters {
//    }

    private class TestClassRunnerForParameters extends
            BlockJUnit4ClassRunner {
        private final int fParameterSetNumber;

        private final List<Object[]> fParameterList;

        TestClassRunnerForParameters(Class<?> type,
                List<Object[]> parameterList, int i) throws InitializationError {
            super(type);
            fParameterList= parameterList;
            fParameterSetNumber= i;
        }

        @Override
        public Object createTest() throws Exception {
            return getTestClass().getOnlyConstructor().newInstance(
                    computeParams());
        }

        private Object[] computeParams() throws Exception {
            try {
                return fParameterList.get(fParameterSetNumber);
            } catch (ClassCastException e) {
                throw new Exception(String.format(
                        "%s.%s() must return a Collection of arrays.",
                        getTestClass().getName(), getParametersMethod(
                                getTestClass()).getName()));
            }
        }

        @Override
        protected String getName() {
            return String.format("[%s]", fParameterSetNumber);
        }

        @Override
        protected String testName(final FrameworkMethod method) {
            return String.format("%s[%s]", method.getName(),
                    fParameterSetNumber);
        }

        @Override
        protected void validateConstructor(List<Throwable> errors) {
            validateOnlyOneConstructor(errors);
        }

        @Override
        protected Statement classBlock(RunNotifier notifier) {
            return childrenInvoker(notifier);
        }
        
        @Override
        protected Annotation[] getRunnerAnnotations() {
            return new Annotation[0];
        }
        
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

    }

    private final ArrayList<Runner> runners= new ArrayList<Runner>();

    /**
     * Only called reflectively. Do not use programmatically.
     */
    public ParameterizedIgnorable(Class<?> klass) throws Throwable {
        super(klass, Collections.<Runner>emptyList());
        List<Object[]> parametersList= getParametersList(getTestClass());
        for (int i= 0; i < parametersList.size(); i++)
            runners.add(new TestClassRunnerForParameters(getTestClass().getJavaClass(),
                    parametersList, i));
    }

    @Override
    protected List<Runner> getChildren() {
        return runners;
    }

    @SuppressWarnings("unchecked")
    private List<Object[]> getParametersList(TestClass klass)
            throws Throwable {
        return (List<Object[]>) getParametersMethod(klass).invokeExplosively(
                null);
    }

    private FrameworkMethod getParametersMethod(TestClass testClass)
            throws Exception {
        List<FrameworkMethod> methods= testClass
                .getAnnotatedMethods(org.junit.runners.Parameterized.Parameters.class);
        for (FrameworkMethod each : methods) {
            int modifiers= each.getMethod().getModifiers();
            if (Modifier.isStatic(modifiers) && Modifier.isPublic(modifiers))
                return each;
        }

        throw new Exception("No public static parameters method on class "
                + testClass.getName());
    }
    
}
