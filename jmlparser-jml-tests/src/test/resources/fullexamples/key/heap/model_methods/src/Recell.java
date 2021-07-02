final class Recell extends Cell {

    int oval;

    /*@ model \locset footprint() { return \set_union(\singleton(this.val), \singleton(this.oval)); } @*/

    /*@ model two_state boolean post_set(int x) { return (get() == x &&  oval == \old(get())); } @*/

    /*@ ensures get() == \old(oval); assignable footprint(); @*/
    void undo() { this.val = this.oval; }

    void set(int x) { oval = val; val = x; }

}

