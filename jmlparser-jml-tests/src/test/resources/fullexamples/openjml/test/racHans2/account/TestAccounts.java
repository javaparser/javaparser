package account;

import unitTest.TestCase;


/*
 * OpenJML call:
 * 
 * cd /home/hso/java/SCJ_Workspace/OpenJMLTest
 *
 *  Accounts:
 *  
 * java -jar /home/hso/java/SCJ_Workspace/OpenJMLTest/lib/openjml.jar -cp ./bin/ -d /home/hso/java/SCJ_Workspace/OpenJMLTest/bin/ -nowarn -noInternalSpecs -rac -racCheckAssumptions -racJavaChecks -nullableByDefault -showNotImplemented -specspath ./specs ./src/account/Accounts.java
 *
 */
public class TestAccounts extends TestCase {

	static final int testCount = 1;

	public TestAccounts(String name) {
	    super(name);
	}

	public void test(int i) {
		
		switch (i) {
		
		  // public Accounts(Frame[] frames)
		  case 1: // frame array with a null element
                  // new CyclicSchedule (new Frame[] {frame0, null, frame2});
			try {
			  Object frame0 = new Integer(0);
			  Object frame2 = new String("2");
			  new Accounts (new Object[] {frame0, null, frame2});
			  assert false; 
			}
	        catch (IllegalArgumentException e) {
	        }; 
			break;
		  default:
			break;
		}
	}
}
