final class Tree {

    /*@ nullable @*/ Tree left; 
    /*@ nullable @*/ Tree right;
    int data;

    //@ ghost instance int height;

    /*@ model_behavior 
          requires treeInv();
          ensures true;
          accessible footprint();
          measured_by height;
          helper model \locset footprint() {
             return \set_union(
               this.*,
               \set_union(
                  left == null? \empty: left.footprint(), 
                  right == null? \empty: right.footprint()
               )
             );
          } @*/

    /*@ model_behavior 
          requires true;
          ensures true;
          accessible footprint();
          measured_by height;
          helper model boolean treeInv() {
             return (
                    (left != right || left == null || right == null)
                 && 0 <= height
                 && (left==null || (left.height < height && \disjoint(this.*, left.footprint())
                          && left.treeInv()))  
                 && (right==null || (right.height < height && \disjoint(this.*, right.footprint())
                          && right.treeInv()))
                 && (left==null || right==null || \disjoint(left.footprint(), right.footprint()))) ;
          } @*/

    /*@ model_behavior 
          requires treeInv();
          ensures true;
          accessible footprint();
          measured_by height;
          helper model \seq treeRep() {
             return \seq_concat(
               (left==null) ? \seq_empty: left.treeRep(),
               \seq_concat(
                  \seq_singleton(this),
                  (right==null) ? \seq_empty: right.treeRep()
               )
             );
          } @*/


    /*@ model_behavior 
          requires treeInvUntilLeft(t) && t.treeInv();
          ensures true;
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model \locset footprintUntilLeft(Tree t) {
             return (
               t == this ? \empty : \set_union(
                 this.*,
                 \set_union(
                    (left==null) ? \empty : left.footprintUntilLeft(t),
                    (right==null) ? \empty : right.footprint()
                 )
               )
             );
          } @*/


    /*@ model_behavior 
          requires t.treeInv();
          ensures true;
          accessible \set_union(footprintUntilLeft(t), \singleton(t.height));
          measured_by height;
          helper model boolean treeInvUntilLeft(Tree t) {
             return (t == this || 
                      ( (left != right || left == null || right == null)
                     && 0 <= height 
                     && (left==null ||
                          (left.height < height && \disjoint(this.*, left.footprintUntilLeft(t))
                         && left.treeInvUntilLeft(t)))  
                     && (right==null ||
                       (right.height < height && \disjoint(this.*, right.footprint())
                       && right.treeInv()))
                     && (left==null || right==null ||
                          \disjoint(left.footprintUntilLeft(t), right.footprint()))
                      )
                    );
          } @*/


    /*@ model_behavior 
          requires treeInvUntilLeft(t) && t.treeInv();
          ensures true;
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model \seq treeRepUntilLeft(Tree t) {
            return (
                (t == this) ? \seq_empty : 
                \seq_concat(
                  (left == null) ? \seq_empty : left.treeRepUntilLeft(t), 
                  \seq_concat(
                     \seq_singleton(this),
                     (right == null) ? \seq_empty : right.treeRep()
                  )
                )
            );
          } @*/

    
    /*@ model_behavior
          requires treeInvUntilLeft(t) && t.treeInv(); 
          requires \disjoint(footprintUntilLeft(t), t.footprint());
          ensures \result ==> (t.left == null || leftSubTree(t.left));
          ensures \result ==> (t.left == null || treeInvUntilLeft(t.left));
          ensures \result ==> (treeRep() == \seq_concat(t.treeRep(), treeRepUntilLeft(t)));
          ensures \result ==> (footprint() == \set_union(footprintUntilLeft(t), t.footprint()));
          ensures \result ==> (treeInv() <==> (treeInvUntilLeft(t) && t.treeInv()));
          ensures \result ==> (t.left == null ||
             (treeRepUntilLeft(t.left) ==
                \seq_concat(
                  \seq_singleton(t),
                  \seq_concat((t.right == null) ? \seq_empty : t.right.treeRep(), treeRepUntilLeft(t))
                )
              )
          );
          ensures \result ==> (t.left == null || 
              (footprintUntilLeft(t.left) == 
                \set_union(t.*,
                    \set_union(
                       (t.right == null) ? \empty : t.right.footprint(),
                       footprintUntilLeft(t)
                    )
                )
              )
          );
          accessible footprintUntilLeft(t);
          measured_by height;
          helper model boolean leftSubTree(Tree t) {
            return (
              t == this ||
              (left != null && left.leftSubTree(t))
            ); 
          }
      @*/

     //@ invariant true;
     //@ accessible \inv : \nothing;

    /*@ normal_behavior
      @ requires t.treeInv();
      @ ensures \result == null ==> \old(t.treeRep() == \seq_singleton(t));
      @ ensures \result != null ==> (\result.treeInv() &&
          (\exists Tree p;
              \old(t.treeRep()) == \seq_concat(\seq_singleton(p), \result.treeRep())
          ));
      @ assignable t.footprint();
      @*/
    static /*@ helper nullable @*/ Tree deleteMin (Tree t) {
       Tree tt, p2, p;

       p = t.left;
       if (p == null) {
           t = t.right;
       } else {
           p2 = t; tt = p.left;

           /*@ loop_invariant t.treeInv();
             @ loop_invariant t.treeInvUntilLeft(p2);
             @ loop_invariant p != null;
	     @ loop_invariant p.treeInv();
             @ loop_invariant p2 != null;
             @ loop_invariant p2.treeInv();
             @ loop_invariant tt == null || tt.treeInv();
             @ loop_invariant p.left == tt;
             @ loop_invariant p2.left == p;
             @ loop_invariant t.leftSubTree(p2);
             @ loop_invariant \subset(\singleton(p2.left), t.footprint());
             // These two are actually redundant (I am almost sure)
             // @ loop_invariant t.treeRep() == \seq_concat(p2.treeRep(), t.treeRepUntilLeft(p2));
             // @ loop_invariant t.footprint() == \set_union(t.footprintUntilLeft(p2), p2.footprint());
             @ loop_invariant \disjoint(t.footprintUntilLeft(p2), p2.footprint());
             @ decreasing tt == null ? 0 : (tt.height+1);
             @ assignable \strictly_nothing;
             @*/
           while (tt != null) {
               p2 = p; p = tt; tt = p.left;
           }
           p2.left = p.right;
       }
       return t;
    }

}
