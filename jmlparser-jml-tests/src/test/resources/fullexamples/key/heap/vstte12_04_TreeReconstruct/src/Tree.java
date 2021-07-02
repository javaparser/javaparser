class Tree {
    
    final /*@ nullable @*/ Tree left;
    final /*@ nullable @*/ Tree right;
    
    //@ final ghost \seq heights;
    
    //@ invariant left == null <==> right == null;

    /*@ invariant (\forall int i; 0<=i && i<heights.length; 
      @               (int)heights[i] == heights[i]);
      @*/

    /*@ invariant left != null ==>
      @  (heights == \dl_seqInc(\seq_concat(left.heights,right.heights))); 
      @*/

    /*@ invariant left == null ==>
      @  heights == \seq_singleton(0);
      @*/
    
    /*@ normal_behavior
      @ ensures left == null && right == null;
      @ ensures heights == \seq_singleton(0);
      @ pure
      @*/
    public Tree() {
        //@ set heights = \seq_singleton(0);
	this.left = null;
	this.right = null;
    }
    
    /*@ normal_behavior
      @ ensures left == l && right == r;
      @ ensures heights == \dl_seqInc(\seq_concat(l.heights,r.heights));
      @ ensures (\forall int i; 0<=i && i<heights.length; 
      @               (int)heights[i] == heights[i]);
      @ pure
      @*/
    public Tree(Tree l, Tree r){
        //@ set heights = \dl_seqInc(\seq_concat(l.heights,r.heights));
        left = l; right = r;
    }

    /*@ behaviour
      @   requires \invariant_for(s);
      @   requires d >= 0;
      @   ensures  \invariant_for(s);
      @   ensures s.p > \old(s.p);
      @   ensures \result.heights.length == s.p - \old(s.p);
      @   ensures (\forall int i; 0<=i && i<\result.heights.length; 
      @                 (int)\result.heights[i] + d == s.a[\old(s.p)+i]);
      @   ensures \fresh(\result);
      @   measured_by s.max-d;
      @   assignable s.p;
      @   signals (TreeException) true;
      @   signals_only TreeException;
      @*/
    static Tree build(int d, List s) throws TreeException {
        if (s.isEmpty()) {
            throw new TreeException();
        }

        int h = s.head();
        if (h < d) {
            throw new TreeException();
        }

        if (h == d){
            s.pop();
            return new Tree();
        }

        Tree l = build(d+1,s);
        Tree r = build(d+1,s);
        return new Tree(l,r);
    }
    
    /*@ public behavior
      @   requires (\forall int i; 0<=i && i < array.length; array[i] >= 0);
      @   ensures array.length == \result.heights.length;
      @   ensures (\forall int i; 0<=i && i<array.length; array[i] == (int)\result.heights[i]);
      @   signals (TreeException) true;
      @   signals_only TreeException;
      @*/
    static Tree build(int[] array) throws TreeException {
	List s = new List(array);
        Tree t = build(0, s);
        if (!s.isEmpty()) 
	    throw new TreeException();

        return t;
    }
    

    /*@ public behaviour
      @   ensures \result.heights[0] == 1; 
      @   ensures \result.heights[1] == 3;
      @   ensures \result.heights[2] == 3;
      @   ensures \result.heights[3] == 2;
      @   ensures \result.heights.length == 4;
      @   signals (Exception) false;
      @*/
    static Tree harness1() throws TreeException {
	int[] orig = new int[]{1,3,3,2};
	Tree t = build(orig);
	return t;
    }

    
    /*@ 
      @ ensures false;
      @ signals (TreeException) true;
      @ signals_only TreeException;
      @*/
    static Tree harness2() throws TreeException {
        int[] orig = new int[]{1,3,2,2};
        return build(orig);
    }


    public String toString() {
	if(left == null) {
	    return "Leaf";
	} else {
	    return "Node(" + left + "," + right + ")";
	}
    }
}