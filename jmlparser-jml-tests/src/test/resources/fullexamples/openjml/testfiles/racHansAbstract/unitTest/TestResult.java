
package unitTest;

import java.util.Enumeration;
import java.util.Vector;

/**
 * A <code>TestResult</code> collects the results of executing a test case.
 * It is an instance of the Collecting Parameter pattern. The test
 * framework distinguishes between <i>failures</i> and <i>errors</i>. <br>
 * A failure is anticipated and checked for with assertions. <br>
 * Errors are unanticipated problems like an
 * <code>ArrayIndexOutOfBoundsException</code>.
 * 
 * @see Test
 */
public class TestResult
{
  protected Vector<TestFailure> fFailures; 
  protected Vector<TestFailure> fErrors;
  
  protected Vector<TestFailure> fJMLErrors;
  
  protected int fRunTests;

  private boolean fStop;

  public TestResult ()
  {
    fFailures  = new Vector<TestFailure>();    
    fErrors    = new Vector<TestFailure>();
    fJMLErrors = new Vector<TestFailure>();
    
    fRunTests = 0;
    fStop = false;
  }

  /**
   * Adds an error to the list of errors. The passed in exception caused
   * the error.
   */
  public void addError (Test test, Throwable t)
  {
    fErrors.addElement(new TestFailure(test, t));
  }

  /**
   * Adds a failure to the list of failures. The passed in exception caused
   * the failure.
   */
  public void addFailure (Test test, AssertionFailedError t)
  {
    fFailures.add(new TestFailure(test, t));
  }
  
  public void addJMLError (Test test, Error t)
  {
	fJMLErrors.addElement(new TestFailure(test, t));
  }

  /**
   * Informs the result that a test was completed.
   */
  public void endTest (Test test)
  {
  }

  /**
   * Gets the number of detected JML errors.
   */
  public int JMLerrorCount ()
  {
    return fJMLErrors.size();
  }

  /**
   * Returns an Enumeration for the JML errors
   */
  public Enumeration<TestFailure> JMLerrors ()
  {
    return fJMLErrors.elements();
  }

  /**
   * Gets the number of detected failures.
   */
  public int failureCount ()
  {
    return fFailures.size();
  }

  /**
   * Returns an Enumeration for the failures
   */
  public Enumeration<TestFailure> failures ()
  {
    return fFailures.elements();
  }
 
  public int errorCount ()
  {
    return fErrors.size();
  }

  /**
   * Returns an Enumeration for the errors
   */
  public Enumeration<TestFailure> errors ()
  {
    return fErrors.elements();
  }
  
  /**
   * Runs a TestCase.
   */
  protected void run (final TestCase test)
  {
    //devices.Console.println("1 TestResult.run");

    startTest(test);
    Protectable p = new Protectable()
      {
        public void protect () throws Throwable
        {
          test.runBare();
        }
      };
      
    runProtected(test, p);
    //devices.Console.println("2 TestResult.run");
    endTest(test);

  }

  /**
   * Gets the number of run tests.
   */
  public int runCount ()
  {
    return fRunTests;
  }

  /**
   * Runs a TestCase.
   */
  public void runProtected (final Test test, Protectable p)
  {
    try
    {
      //devices.Console.println("TestResult.runProtected");
      p.protect();
    }
    catch (AssertionFailedError e)
    {
      //devices.Console.println("TestResult.runProtected: failure");
      
      addFailure(test, e);
    }
    catch (ThreadDeath e)
    { // don't catch ThreadDeath by accident
      throw e;
    }
    catch (Throwable e)
    {
      //devices.Console.println("TestResult.runProtected: error");
      
      addError(test, e);
    }
  }

  /**
   * Checks whether the test run should stop
   */
  public boolean shouldStop ()
  {
    return fStop;
  }

  /**
   * Informs the result that a test will be started.
   */
  public void startTest (Test test)
  {
    final int count = test.countTestCases();
    
    {
      fRunTests += count;
    }
  }

  /**
   * Marks that the test run should stop.
   */
  public void stop ()
  {
    fStop = true;
  }

  /**
   * Returns whether the entire test was successful or not.
   */
  public boolean wasSuccessful ()
  {
    return failureCount() == 0 && errorCount() == 0 && JMLerrorCount () == 0;
  }
}