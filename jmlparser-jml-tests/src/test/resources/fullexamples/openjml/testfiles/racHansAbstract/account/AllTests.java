package account;

import java.util.Enumeration;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest.TestCase;
import unitTest.TestFailure;
import unitTest.TestResult;
import unitTest.TestSuite;

public class AllTests
{
  static final TestResult result = new TestResult(); 
  
  static final String name = "Account";
  
  public static void main (String[] args)
  {
    TestSuite suite = new TestSuite();    
    
    //suite.addTest(test_Account);
    //suite.addTest(test_AccountStub);
    suite.addTest(test_ConcreteAccount);
    
    suite.run(result);

    System.out.println("\nTest of " + name + ":");
    System.out.println("    Test cases:  " + result.runCount());
    System.out.println("    Test errors: " + result.errorCount());
    System.out.println("    JML errors:  " + result.JMLerrorCount());
    
    if (result.errorCount() > 0)
    {
    	System.out.println("\nTest errors are in:");

      for (Enumeration<TestFailure> e = result.errors(); 
          e.hasMoreElements();)
      {
    	  System.out.println("" + e.nextElement());
      }
    }
    if (result.JMLerrorCount() > 0)
    {
    	System.out.println("\nJML errors are in:");

      for (Enumeration<TestFailure> e = result.JMLerrors(); 
          e.hasMoreElements();)
      {
    	  System.out.println("" + e.nextElement());
      }
    }
  }
  
//  public static TestCase test_Account = new TestAccount("Account")
//  {
//    public void runTest ()
//    {
//      int i = 1;
//      try
//      {        
//        for ( ; i <= TestAccount.testCount; i++)
//          test(i);  
//      }
//      catch (JmlAssertionError e) { 
//        AllTests.result.addJMLError(this, e); 
//        this.setCaseNumber(i); }
//      catch (Throwable e) { 
//        AllTests.result.addError(this, e); 
//        this.setCaseNumber(i); }
//    }
//  };
  
//  public static TestCase test_AccountStub = new TestAccountStub("AccountStub")
//  {
//    public void runTest ()
//    {
//      int i = 1;
//      try
//      {        
//        for ( ; i <= TestAccountStub.testCount; i++)
//          test(i);  
//      }
//      catch (JmlAssertionError e) { 
//        AllTests.result.addJMLError(this, e); 
//        this.setCaseNumber(i); }
//      catch (Throwable e) { 
//        AllTests.result.addError(this, e); 
//        this.setCaseNumber(i); }
//    }
//  };
  
  public static TestCase test_ConcreteAccount = new TestConcreteAccount("ConcreteAccount")
  {
    public void runTest ()
    {
      int i = 1;
      try
      {        
        for ( ; i <= TestConcreteAccount.testCount; i++)
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
