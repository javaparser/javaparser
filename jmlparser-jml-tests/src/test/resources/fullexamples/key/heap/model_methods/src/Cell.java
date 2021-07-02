class Cell {
    int val;

    /*@ model_behavior
      @ ensures \subset(\result, this.* );
      @ ensures \subset(\singleton(this.val), \result);
      @ accessible \nothing;
      @ model \locset footprint() { return \singleton(this.val); }
      @*/

    /*@ model_behavior
      @ ensures \result ==> get()==x;
      @ accessible footprint();
      @ model two_state boolean post_set(int x) { return (get() == x); }
      @*/

    /*@ ensures \result == val;
      @ accessible footprint();
      @*/
    /*@ strictly_pure*/ int get() { return val; }

    /*@ ensures post_set(v); assignable footprint(); @*/
    void set(int v) { val = v; }
}
