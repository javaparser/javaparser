package account;

import java.util.Enumeration;

//import javax.scj.util.Const;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest.TestCase;
import unitTest.TestFailure;
import unitTest.TestResult;
import unitTest.TestSuite;

public class AllTests
{
  static final TestResult result = new TestResult();

  static final String name = "Accounts";

  public static void main (String[] args)
  {
	//Const.setDefaultErrorReporter();

    TestSuite suite = new TestSuite();

    suite.addTest(test_Accounts);

    suite.run(result);

	printResult();
  }

  private static void printResult() {
	System.out.println("\nTest of " + name + ":");
	System.out.println("    Test cases:  " + result.runCount());
	System.out.println("    Test errors: " + result.errorCount());
	System.out.println("    JML errors:  " + result.JMLerrorCount());

	if (result.errorCount() > 0) {
		System.out.println("\nTest errors are in:");

		for (Enumeration<TestFailure> e = result.errors(); e.hasMoreElements();) {
			System.out.println("" + e.nextElement());
		}
	}
	if (result.JMLerrorCount() > 0) {
		System.out.println("\nJML errors are in:");

		for (Enumeration<TestFailure> e = result.JMLerrors(); e.hasMoreElements();) {
			System.out.println("" + e.nextElement());
		}
	}
  }

  public static TestCase test_Accounts = new TestAccounts("Accounts")
  {
    public void runTest ()
    {
      int i = 1;
      try
      {
        for ( ; i <= TestAccounts.testCount; i++)
          test(i);
      }
      catch (JmlAssertionError e) {
        AllTests.result.addJMLError(this, e);
        this.setCaseNumber(i); }
      catch (Throwable e) {
        AllTests.result.addError(this, e);
        this.setCaseNumber(i); }
    }
  };

}
