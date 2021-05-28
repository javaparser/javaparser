class Cell {
    //@invariant this.*;

    /*@ model_behavior
      @ ensures \subset(\result, this.* );
      @ ensures \subset(\locset(this.val), \result);
      @ accessible \nothing;
      @ model \locset footprint() { return \locset(this.val); }
      @*/
}

