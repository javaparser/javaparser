package unitTest;

public interface Test
{
  
  /**
   * Counts the number of test cases that will be run by this test.
   */
  public abstract int countTestCases();
  
  /**
   * Runs a test and collects its result in a TestResult instance.
   */
  public abstract void run(TestResult result);

}
