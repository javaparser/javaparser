/* 
Attention: To generate correct tests (tests that satisfy the precondition)
 for the methods foo1 and foo2, the Integer Bound in Options -> SMT Solver Options must be
 set to at least 6 (the default is 3). 
 
By default KeY does not know the classes of the standard Java runtime environment,
 therefore the statements "System.out.println(...)" are commented out for 
 symbolic execution. After test case generation this file is copied to a subfolder
 of the testFiles folder specified in the Test Suite Generation window.
 You can uncomment the "System.out.println(...)" statements when compiling the file
 for test execution in order to see which branches are executed by the tests.
 
@author Christoph Gladisch
*/

class ContractLoopInvariantTest {

  void A(){ /*System.out.println("A");*/ }

  void B(){ /*System.out.println("B");*/ }

  void C(){ /*System.out.println("C");*/ }

  /*@ public normal_behavior
    requires 0<=n; ensures true;
  @*/
  public void foo1(int n){
    int i=0;
    /*@ loop_invariant 0<=i && i<=n;
	decreases n-i;
    @*/
    while(i < n){
      if(i==10){ A();}
      B();
      i++;
    }
    if(i==20){ C(); }
  }


  public int i;
  /*@ public normal_behavior
    requires i<=n; ensures i==n;
    modifies i; @*/
  public void D(int n){
    /*System.out.println("D");*/
    while(i < n){ i++; A(); }
  }

  /*@ public normal_behavior
    requires i<=n; ensures i==n;
    modifies i; @*/
  public void foo2(int n){
    D(n);
    if(i==20){ C(); }
  }

}
