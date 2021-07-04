public class UniqueList {

	private /*@ spec_public */ int[] values;
	private /*@ spec_public */ int length;

	/* public invariant (\forall int i, j; 
	     0 <= i && i < length - 1 &&
	     1 <= j && j < length &&
	     i < j; values[i] != values[j]
	   );
	  */
	
/*	{
	    new org.jmlspecs.utils.Utils.ValueBool() {
	    public boolean value(Object[] args) { return true;}
	    }.value(null);
	}
*/
	/* @ public invariant (\forall int i; 
      @   0 <= i && i < length - 1;
      @   (\forall int j; 1 <= j && j < length && i < j; values[i] != values[j])
      @ );
      @*/

	public UniqueList(){
		values = new int[10];
		length = 0;
	}
	
	/*@ requires length < 10;
	  @ ensures length == \old(length) + 1;
	  @ requires (\forall int i; 0 <= i && i < length; values[i] != value);
	  @*/
	public void add(int value){
		values[length] = value;
		length++;
	}
	
	/*@ requires index < length;
	  @ ensures \result == values[index];
	  @*/
	public /*@ pure */ int getValue(int index){
		return values[index];
	}
	
	/*@
	  @ requires index1 < length;
	  @ requires index2 < length;
	  @ ensures values[index1] == \old(values[index2]);
	  @ ensures values[index2] == \old(values[index1]);
	  @*/
	public void swap(int index1, int index2){
		int temp = values[index1];
		values[index1] = values[index2];
		values[index2] = temp;
	}
	
	public static void main(String[] args){
		UniqueList list = new UniqueList();
		list.add(4);
		list.add(5);
		list.add(6);
		list.swap(0,2);
		list.add(6);
	}
}