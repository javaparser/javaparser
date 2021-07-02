public class RingBuffer {
    
    int[] data;
    int first;
    int len;
    
    //@ ghost \seq list;
    //@ invariant list.length == len;
    //@ invariant data.length > 0;
    //@ invariant 0 <= first && first < data.length;
    //@ invariant 0 <= len && len <= data.length;
    //@ invariant (\forall int i; 0 <= i && i < len; list[i] == data[modulo(first+i)]);
        
    /*@ normal_behavior
      @ requires n >= 1;
      @ assignable this.*;
      @ ensures list == \seq_empty;
      @ ensures first == 0;
      @ ensures data.length == n;
     */
    RingBuffer(int n){
        //@ set list = \seq_empty;
        data = new int[n];
    }
    
    /*@ normal_behavior
      @ ensures list == \seq_empty;
      @ ensures first == \old(first);
      @ assignable len,list;
      @*/
    void clear(){
        //@ set list = \seq_empty;
        len = 0;
    }
    
    /*@ normal_behavior
      @ requires !isEmpty();
      @ ensures \result == list[0];
      @ pure
      @*/
    int head() {
        return data[first];
    }
    
    /*@ normal_behavior
      @ requires !isFull();
      @ ensures list == \seq_concat(\old(list),\seq_singleton(x));
      @ assignable len,list,data[modulo(first+len)];
      @*/
    void push(int x){
        int pos = modulo(first+len);

        data[pos] = x;
        //@ set list = \seq_concat(list,\seq_singleton(x));
        len++;
    }
    
    /*@ normal_behavior
      @ requires !isEmpty();
      @ ensures list == \seq_sub(\old(list),1,\old(list.length));
      @ ensures first == modulo(\old(first)+1);
      @ ensures \result == \old(data[first]);
      @ assignable first,len,list;
      @*/
    int pop(){
        int r = data[first];
        first = modulo(first+1);

        len--;
        //@ set list = \seq_sub(list,1,\seq_length(list));
        return r;
    }
    
    
    // helper methods
    /*@ normal_behavior
      @ ensures \result == (len == 0);
      @ strictly_pure helper
      @*/
    boolean isEmpty() {
        return len == 0;
    }
    
    /*@ normal_behavior
      @ ensures \result == (len  == data.length);
      @ strictly_pure
      @*/
    boolean isFull() {
        return len == data.length;
    }
    
    /*@ public normal_behaviour
      @   ensures x >= 0 && x < data.length ==> \result == x;
      @   ensures x >= data.length && x < data.length + data.length ==>
      @       \result == x - data.length;
      @   strictly_pure
      @*/
    int modulo(int x) {
	return x < data.length ? x : x - data.length;
    }
    
    // Harness
    
    //@ ensures true;
    //@ signals (Exception) false;
    static void test (int x, int y, int z){
        RingBuffer b = new RingBuffer(2);
        b.push(x);
        b.push(y);
        int h = b.pop();
        assert h == x;
        b.push(z);
        h = b.pop();
        assert h == y;
        h = b.pop();
        assert h == z;
    }
 
}
