
 public class AbsoluteValue{
	//@ requires num >= 0;
	//@ ensures \result == num;
	//@ ensures \result >= 0;

	//@ also

	//@ requires num < 0 && num > Integer.MIN_VALUE;
	//@ ensures \result == -num; 
	//@ ensures \result >= 0;
	public /*@ pure @*/ int IntAbsolute(int num){
		if(num >= 0)
			return num;
		else
			return -num;
	}


	//@ requires num >= 0;
	//@ ensures \result == num;
	//@ ensures \result >= 0;

	//@ also

	//@ requires num < 0 && num > Long.MIN_VALUE;
	//@ ensures \result == -num; 
	//@ ensures \result >= 0;
	public /*@ pure @*/ long LongAbsolute(long num){
		if(num >= 0)
			return num;
		else
			return -num;	
	}
}
