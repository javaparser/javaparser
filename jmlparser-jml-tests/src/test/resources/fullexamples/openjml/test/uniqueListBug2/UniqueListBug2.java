// Code is buggy

public class UniqueListBug2 {

	private /*@ spec_public */ int[] values;
	private /*@ spec_public */ int length;

	public UniqueListBug2(){
		values = new int[10];
		length = 0;
	}
	
	/*@ requires length < 10;
	  @ requires !contains(value);
	  @ ensures length == \old(length) + 1;
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
	
	
	
	/*@
	  @ requires contains(value);
	  @ ensures !contains(value);
	  @ ensures \old(values)[\result] == value;
	  @ ensures \result == \old(find(value));
	  @ ensures length == \old(length) - 1;
	  @*/
	
	public int removeValue(int value) {
		int index = find(value);
		System.out.println("\\old(values)[\\result]: " + values[index]);
		for(int i = index; i < length; i++){
			values[index] = values[index] + 1; 
		}
		length -= 1;
		System.out.println("value: " + value + " " + index + " " + values[index]);
		return index;
	}
	
	
	/*@
	  @ ensures \result >= 0;
	  @ ensures \result <= length;
	  @ ensures contains(value) ==> value == values[\result];
	  @ ensures !contains(value) ==> \result == length;
      @ pure
	  @*/
	public int find(int value) {
		for(int i = 0; i < length; i++){
			if(values[i] == value){
				return i;
			}
		}
		return length;
	}
	
	/*@
	  @ ensures \result == (\exists int i; 0 <= i && i < length; value == values[i]);
      @ pure
	  @*/
	public boolean contains(int value){
		for(int i = 0; i < length; i++){
			if(values[i] == value){
				return true;
			}
		}
		return false;
	}

	public static void main(String[] args){
		UniqueListBug2 list = new UniqueListBug2();
		list.add(4);
		list.add(5);
		list.add(6);
		list.removeValue(6);
	}
}