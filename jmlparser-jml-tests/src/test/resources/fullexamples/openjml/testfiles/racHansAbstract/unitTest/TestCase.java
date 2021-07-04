package unitTest;

//import java.lang.reflect.InvocationTargetException;
//import java.lang.reflect.Method;
//import java.lang.reflect.Modifier;

public abstract class TestCase extends Assert implements Test {
	/**
	 * the name of the test case
	 */
	private String fName;
	
	// Switch case number
	private int caseNumber;
	
	public void setCaseNumber(int number)
	{
		caseNumber = number;
	}

	/**
	 * No-arg constructor to enable serialization. This method is not intended
	 * to be used by mere mortals without calling setName().
	 */
	public TestCase() {
		fName = null;
	}

	/**
	 * Constructs a test case with the given name.
	 */
	public TestCase(String name) {
		fName = name;
	}

	/**
	 * Counts the number of test cases executed by run(TestResult result).
	 */
	public int countTestCases() {
		return 1;
	}

	public void run(TestResult result) {
		//devices.Console.println("TestCase.run begin");
		result.run(this);
		//devices.Console.println("TestCase.run end");
	}

	/**
	 * Runs the bare test sequence.
	 * 
	 * @exception Throwable
	 *                if any exception is thrown
	 */
	public void runBare() throws Throwable {
		Throwable exception = null;
		setUp();
		try {
			runTest();
		} catch (Throwable running) {
			exception = running;
		} finally {
			try {
				tearDown();
			} catch (Throwable tearingDown) {
				if (exception == null)
					exception = tearingDown;
			}
		}
		if (exception != null)
			throw exception;
	}

	/**
	 * Override to run the test and assert its state.
	 * 
	 * @exception Throwable
	 *                if any exception is thrown
	 */
	protected void runTest() throws Throwable {
		/*
		 * assertNotNull(fName); // Some VMs crash when calling
		 * getMethod(null,null); Method runMethod= null; try { // use getMethod
		 * to get all public inherited // methods. getDeclaredMethods returns
		 * all // methods of this class but excludes the // inherited ones.
		 * runMethod= getClass().getMethod(fName, (Class[])null);
		 * 
		 * System.out.println ("1 TestCase.runTest: " + runMethod);
		 * 
		 * } catch (NoSuchMethodException e) {
		 * fail("Method \""+fName+"\" not found"); } if
		 * (!Modifier.isPublic(runMethod.getModifiers())) {
		 * fail("Method \""+fName+"\" should be public"); }
		 * 
		 * try { System.out.println ("2 TestCase.runTest: " + runMethod);
		 * runMethod.invoke(this, (Object[])new Class[0]); } catch
		 * (InvocationTargetException e) { e.fillInStackTrace(); throw
		 * e.getTargetException(); } catch (IllegalAccessException e) {
		 * e.fillInStackTrace(); throw e; }
		 */
	}

	/**
	 * Sets up the fixture, for example, open a network connection. This method
	 * is called before a test is executed.
	 */
	protected void setUp() throws Exception {
	}

	/**
	 * Tears down the fixture, for example, close a network connection. This
	 * method is called after a test is executed.
	 */
	protected void tearDown() throws Exception {
	}
	/**
	 * Returns a string representation of the test case
	 */
	public String toString() {
	    return getName() + "(" + getClass().getName() + ")" + "\nTest number is "+ caseNumber;
	}
	/**
	 * Gets the name of a TestCase
	 * @return returns a String
	 */
	public String getName() {
		return fName;
	}
	/**
	 * Sets the name of a TestCase
	 * @param name The name to set
	 */
	public void setName(String name) {
		fName= name;
	}
}
