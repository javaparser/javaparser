package stack;


public interface Stack{
	/*@
	  @public invariant count()>=0;
	  @*/

	//-RAC@ public instance model int count;
	
	//-RAC@ ensures \result == count;
	//@ pure
	//@ helper
	int count();

	//@ requires i>=1 && i<=count();
	//@ pure
	int itemAt (int i);

	//@ ensures \result==(count()==0);
	//@ pure
	boolean isEmpty ( );

	//-RAC@ assignable count;
	//@ ensures \result ==> count() == \old(count()) + 1;
	//@ ensures \result ==> item==(top());
	//@ ensures (\forall int i; 1<=i && i<=\old(count()); itemAt(i)==\old(itemAt(i)));
	boolean push(int item);

	//@ pure;
	int top();

	boolean remove ( );

}
