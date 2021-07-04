package org.openjml.runners;


/** This class is a minor modification of org.junit.runners.Parameterized. The changes are (1) to log
 *  tests whose assumptions are false as ignored instead of failed, and (2) to allow
 *  inserting the parameter values instead of an index as the name of a test. 
 *  <BR>
 *  The class still uses org.junit.runners.Parameterized.Parameters to identify the data method.
 *  <BR>
 *  The inner class TestClassRunnerForParameters would better be an extension of 
 *  org.junit.runner.Parameterized.TestClassRunnerForParameters, but that class is private to Parameterized.
 *  Also, we would prefer to inherit from Parameterized instead of from Suite, but all the methods
 *  of Parameterized are private and we need to use ParameterizedWithNames.TestClassRunnerForParameters
 *  in the ParameterizedWithNames constructor, so we have to copy all the methods from Parameterized
 *  into this class.
 */
import java.lang.annotation.Annotation;
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
import org.junit.runners.Suite;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.Statement;
import org.junit.runners.model.TestClass;

public class ParameterizedWithNames extends Suite
{
    protected Class<?> klass;  // DRC - a change to the original to make it easy to refer to this input
    private final ArrayList<Runner> runners = new ArrayList<Runner>();

    public ParameterizedWithNames(Class<?> klass) throws Throwable {
        super(klass, Collections.<Runner>emptyList());
        this.klass = klass; // DRC - a change to the original
        List<Object[]> parametersList = getParametersList(getTestClass());
        for (int i = 0; i < parametersList.size(); ++i)
            this.runners.add(new TestClassRunnerForParameters(parametersList, i));
    }

    @Override
    protected List<Runner> getChildren() {
        return this.runners;
    }

    @SuppressWarnings("unchecked")
    private List<Object[]> getParametersList(TestClass klass) throws Throwable {
        return ((List<Object[]>)getParametersMethod(klass).invokeExplosively(null, new Object[0]));
    }

    private FrameworkMethod getParametersMethod(TestClass testClass) throws Exception {
        List<FrameworkMethod> methods = testClass.getAnnotatedMethods(Parameters.class);

        for (FrameworkMethod each : methods) {
            int modifiers = each.getMethod().getModifiers();
            if ((Modifier.isStatic(modifiers)) && (Modifier.isPublic(modifiers))) {
                return each;
            }
        }
        throw new Exception("No public static parameters method on class " + testClass.getName()); //$NON-NLS-1$
    }

    private class TestClassRunnerForParameters extends BlockJUnit4ClassRunner {
        private final int fParameterSetNumber;
        private final List<Object[]> fParameterList;

        TestClassRunnerForParameters(List<Object[]> parameterList, int i) throws InitializationError {
            super(klass);
            this.fParameterList = parameterList;
            this.fParameterSetNumber = i;
        }

        @Override
        public Object createTest() throws Exception {
            return getTestClass().getOnlyConstructor().newInstance(computeParams());
        }

        private Object[] computeParams() throws Exception {
            try {
                return (this.fParameterList.get(this.fParameterSetNumber));
            } catch (ClassCastException e) {
                throw new Exception(String.format("%s.%s() must return a Collection of arrays.", new Object[] { getTestClass().getName(), getTestClass().getName() })); //$NON-NLS-1$
            }
        }
        
        // This method is changed to have the name be a combination of the parameters
        // (This is the whole purpose of this revision of Parameterized)
        public String name() {
            Object[] params = (this.fParameterList.get(this.fParameterSetNumber));
            String s = "";
            boolean first = true;
            for (Object o: params) {
                if (first) first = false; else s = s + ",";
                s = s + toString(o);
            }
            return s;
        }
        
        String toString(Object o) {
        	if (o == null) {
        		return "null";
        	} else if (o.getClass().isArray()) {
                return arrayToString((Object[])o);
            } else if (o instanceof String) {
                return o.toString();
                //return "\"" + o.toString() + "\"";
            } else {
                return o.toString();
            }
            
        }
        
        String arrayToString(Object[] array) {
            String s = "[";
            boolean first = true;
            for (Object o: (Object[])array) {
                if (first) first = false; else s = s + ",";
                s = s + toString(o);
            }
            s = s + "]";
            return s;
        }

        @Override
        protected String getName() {
            // DRC - changed to use the parameter list, rather than the index
            return String.format("[%s]", new Object[] { name() }); //$NON-NLS-1$
        }

        @Override
        protected String testName(FrameworkMethod method) {
            // DRC - changed to use the parameter list, rather than the index
            return String.format("%s[%s]", new Object[] { method.getName(), name() }); //$NON-NLS-1$
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
        protected Annotation[] getRunnerAnnotations()  {
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
}
