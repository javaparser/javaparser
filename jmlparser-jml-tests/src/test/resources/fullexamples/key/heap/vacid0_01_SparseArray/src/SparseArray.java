public class SparseArray {
    //@ public ghost int size;    
    //@ public ghost \locset footprint;
    
    //@ public accessible \inv: size, footprint, \singleton(footprint);
    
    private int[] val, idx, back;
    private int n = 0;
    
    /*@ private invariant size == val.length;
      @ private invariant footprint == \set_union(\singleton(this.val), 
      @                                           \set_union(\singleton(this.idx), 
      @                                                      \set_union(\singleton(this.back),
      @                                                                 \set_union(\singleton(this.n), 
      @                                                                            \set_union(\all_fields(val), 
      @                                                                                       \set_union(\all_fields(idx), 
      @                                                                                                  \all_fields(back)))))));
      @ private invariant val != idx && val != back && idx != back; 
      @ private invariant val.length == idx.length && idx.length == back.length;
      @ private invariant (\forall int x; 0 <= x && x < val.length; 0 <= idx[x] && 0 <= back[x]);
      @ private invariant 0 <= n && n <= val.length;
      @ private invariant (\forall int x; 0 <= x && x < n; back[x] < size);      
      @ private invariant (\forall int x; 0 <= x && x < n; idx[back[x]] == x);
      @*/

    
    
    /*@ normal_behaviour
      @   requires 0 <= sz;
      @   ensures \fresh(footprint);
      @   ensures \disjoint(footprint, \singleton(size));
      @   ensures \disjoint(footprint, \singleton(footprint));
      @   ensures size == sz;
      @   ensures (\forall int x; 0 <= x && x < size; get(x) == 0);
      @*/
    public /*@pure@*/ SparseArray(int sz) {
	val = MemoryAllocator.alloc(sz);
	idx = MemoryAllocator.alloc_unsigned(sz);
	back = MemoryAllocator.alloc_unsigned(sz);
	n = 0;
	//@ set size = sz;
	/*@ set footprint = \set_union(\singleton(this.val), 
	                               \set_union(\singleton(this.idx), 
	                                          \set_union(\singleton(this.back),
	                                                     \set_union(\singleton(this.n), 
	                                                                \set_union(\all_fields(val), 
	                                                                           \set_union(\all_fields(idx), 
	                                                                                      \all_fields(back)))))));
	  @*/ 
    }
    
    
    /*@ normal_behavior
      @   requires 0 <= i && i < size;
      @   accessible footprint;
      @   ensures \result == get(i);
      @*/
    public /*@pure@*/ int get(int i) {
	if(idx[i] < n && back[idx[i]] == i) return val[i];
	else return 0;
    }
    

    /*@ normal_behaviour
      @   requires 0 <= i && i < size;
      @   //requires n == size ==> (idx[i] < n && back[idx[i]] == i);//"free requires"
      @   assignable footprint;
      @   ensures (\forall int x; 0 <= x && x < size && x != i; get(x) == \old(get(x)));
      @   ensures get(i) == v;
      @*/
    public void set(int i, int v) {
	val[i] = v;
	if (!(idx[i] < n && back[idx[i]] == i)) {
	    //assert(n < MAXLEN); // (*), see Verification Tasks
	    idx[i] = n; back[n] = i; n = n + 1;
	}
    }
}
