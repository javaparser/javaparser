public interface IntList {
    
    //@ public ghost instance \locset footprint;
    //@ public ghost instance \seq seq;

    //@ public instance invariant \subset(\singleton(this.seq), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    //@ public instance invariant (\forall int i; 0<=i && i<seq.length; seq[i] instanceof int);
    //@ public accessible \inv: footprint;    
}
