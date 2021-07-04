package sv_esc;


/* Solution: 

*/

class Bag {

  int[] contents; //@ invariant contents != null;
  int n;
  //@ invariant 0 <= n;
  //@ invariant n <= contents.length;

  //@ requires input != null;
  Bag(int[] input) {
    n = input.length;
    contents = new int[n];
    arraycopy(input, 0, contents, 0, n);
  }

  //@ requires b != null;
  Bag(Bag b) {
    contents = new int[0]; // error in code corrected
    this.add(b);
  }

  void removeOnce(int elt) {
    for (int i = 0; i < n; i++) {  // error in code corrected
      if (contents[i] == elt ) {
         n--;
         contents[i] = contents[n];
         return;
      }
    }
  }

  void removeAll(int elt) {
	// @ loop_invariant i>=0 && i<=n+1;
    for (int i = 0; i < n; i++) {  // error in code corrected
      if (contents[i] == elt ) {
         n--;
         contents[i] = contents[n];
      }
    }
  }


  //@ ensures \result >= 0;
  /*@ pure @*/ int getCount(int elt) {
    int count = 0;
    //@ loop_invariant i>=0 && i<=n;
    //@ loop_invariant count >= 0;
    for (int i = 0; i < n; i++) 
      if (contents[i] == elt) count++;
    return count;
  }

  void add(int elt) {
    if (n == contents.length) {
       int[] new_contents = new int[2*n+1]; // error in code corrected
       //@ assert new_contents.length == 2*n+1 ; // this should not fail?
       //@ assert n >= 0;
       //@ assert 2*n+1 > n;
       //@ assert  n < new_contents.length;
       arraycopy(contents, 0, new_contents, 0, n);
       contents = new_contents;
    }
    contents[n]=elt;
    n++;
  }

  //@ requires b != null;
  void add(Bag b) {
    int[] new_contents = new int[n+b.n];
    arraycopy(this.contents, 0, new_contents, 0, n);
    arraycopy(b.contents, 0, new_contents, n, b.n);
    contents = new_contents; 
  }


  //@ requires src != null;
  //@ requires srcOff >=0;
  //@ requires dest != null;
  //@ requires destOff >=0;
  //@ requires length >=0;
  //@ requires srcOff + length <= src.length;
  //@ requires destOff + length <= dest.length;
  //@ assignable dest[*];
  private static void arraycopy(int[] src,
                                int   srcOff,
                                int[] dest,
                                int   destOff,
                                int   length) {
    /*@ loop_invariant i>=0 && i<=length; @*/
	for( int i=0 ; i<length; i++) {
       dest[destOff+i] = src[srcOff+i];
    }
  }
  
}
