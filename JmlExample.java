package java.util;
import java.io.*;

class Cell {
    int val;

    /*@ model_behavior
      @ ensures \subset(\result, this.* );
      @ ensures \subset(\locset(this.val), \result);
      @ accessible \nothing;
      @ model \locset footprint() { return \locset(this.val); }
      @*/
}

