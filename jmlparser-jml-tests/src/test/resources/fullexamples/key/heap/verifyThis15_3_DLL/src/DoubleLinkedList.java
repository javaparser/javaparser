// version 2.0, inspired by Rustan
final class DoubleLinkedList {

    final static class Node {
        /*@ nullable @*/ Node l, r; 
    }

    /*@ nullable @*/ Node head;
    //@ ghost \seq s; // represents the contents
    //@ ghost int len; // represents the number of nodes

    /*@ invariant head == null <==> s == \seq_empty;
      @ invariant s == \seq_empty <==> len == 0;
      @ invariant head != null ==> (Node)s[0] == head && 0 < len;
      @ invariant s.length == len;
      @ invariant (\forall int i; 0 <= i < len; s[i] != null);
      @ invariant (\forall int i; 0 < i < len; ((Node)s[i]).l != null);
      @ invariant (\forall int i; 0 <= i < len - 1; ((Node)s[i]).r != null);
      @ invariant (\forall int i; 0 <= i < len; s[i] instanceof Node);
      @   // there is a beginning
      @ invariant head != null ==> head.l == null;
      @   // ... and an end
      @ invariant head != null ==> ((Node)s[len-1]).r == null;
      @   // double link property
      @ invariant (\forall int i; 0 < i < len; ((Node)s[i]).l == (Node)s[i-1]);
      @ invariant (\forall int i; 0 <= i < len-1; ((Node)s[i]).r == (Node)s[i+1]);
      @   // no cycles
      @ invariant (\forall int i,j; 0 <= i < j && j < len; (Node)s[i] != (Node)s[j]);
      @*/

    /*@ normal_behavior
      @ requires (\forall int i,j; 0 <= i < j && j < nodes.length; nodes[i] != nodes[j])
      @       && (\forall int i; 0 <= i < nodes.length; nodes[i] != null);
      @ ensures s == \dl_array2seq(\old(nodes));
      @*/
    DoubleLinkedList (Node[] nodes) {
        head = null;
        if (nodes.length == 0) return;
        int i = 1;
        //@ set s = \seq_singleton(nodes[0]);

        /*@ loop_invariant 0 < i && i <= nodes.length
          @             && nodes != null
          @             && s != \seq_empty
          @             && 0 < nodes.length
          @             && nodes.length == \old(nodes.length)
          @             && s == (\seq_def int j; 0; i; nodes[j])
          @             && (\forall int j; 0 <= j && j < i; (Node)s[j] == nodes[j])
          @             && (\forall int j; 0 <= j < i; s[j] instanceof Node)
          @             && (\forall int j,k; 0 <= j < k && k < nodes.length; nodes[j] != nodes[k])
          @             && (\forall int j; 0 <= j && j < nodes.length; nodes[j] == \old(nodes[j]))
          @             && (\forall int j; 0 <= j && j < nodes.length; nodes[j] != null)
          @             && (\forall int j; 0 < j && j < i; nodes[j-1].r == nodes[j])
          @             && (\forall int j; 0 < j && j < i; nodes[j].l == nodes[j-1])
          @             && (\forall int j; 0 < j && j < i; ((Node)s[j-1]).r == (Node)s[j])
          @             && (\forall int j; 0 < j && j < i; ((Node)s[j]).l == (Node)s[j-1]);
          @ decreases nodes.length - i;
          @*/
        for (i = 1; i < nodes.length; i++) {
            //@ set s = \seq_concat(s, \seq_singleton(nodes[i]));
            nodes[i-1].r = nodes[i];
            nodes[i].l = nodes[i-1];
        }
        //@ set len = nodes.length;
        nodes[0].l = null;
        nodes[nodes.length-1].r = null;
        head = nodes[0];
    }


    /*@ normal_behavior
      @ requires (Node)s[k] == x;
      @ requires 0 < k < len-1;
      @ ensures s == \old(\seq_concat(\seq_sub(s,0,k),\seq_sub(s,k+1,len))) && len == \old(len) - 1
      @      && x.l == ((Node)s[k]).l && x.r == ((Node)s[k]) && x.l == (Node)s[k-1]
      @      && x.r != null && (\forall int i; 0 <= i < len; x != (Node)s[i]);
      @ assignable s, len, x.l.r, x.r.l;
      @*/
    void remove (Node x, int k) {
        //@ set s = \seq_concat(\seq_sub(s,0,k),\seq_sub(s,k+1,len));
        //@ set len = len - 1;
        x.l.r = x.r;
        x.r.l = x.l;
    }

    /*@ normal_behavior
      @ requires 0 < k < len && x.l == ((Node)s[k]).l && x.r == ((Node)s[k]) && x.l == (Node)s[k-1]
      @       && x.r != null && (\forall int i; 0 <= i < len; x != (Node)s[i]);
      @ ensures s == \old(\seq_concat(\seq_sub(s,0,k),\seq_concat(\seq_singleton(x),\seq_sub(s,k,len)))) && len == \old(len) + 1 && x == (Node)s[k];
      @ assignable s, len, x.l.r, x.r.l;
      @*/
    void unremove (Node x, int k) {
        //@ set s = \seq_concat(\seq_sub(s,0,k),\seq_concat(\seq_singleton(x),\seq_sub(s,k,len)));
        //@ set len = len + 1;
        x.l.r = x;
        x.r.l = x;
    }
 
    /*@ normal_behavior
      @ requires 0 < k < len-1;
      @ requires (Node)s[k] == x;
      @ ensures s == \old(s);
      @*/
    void doUndo (Node x, int k) {
        remove(x,k);
        unremove(x,k);
    }
   
}
