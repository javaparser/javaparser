class Ghost {
    //contract encodes "accessible footprint;"
    /*@ normal_behaviour
      @   requires \inv;
      @   requires arrayDep == \singleton(array);
      @   requires sizeDep == \singleton(size);
      @   requires (\forall int i; arraySlotDep[i] == \singleton(array[i]));
      @   requires (\forall int i; arraySlotDep.length == array.length);
      @   ensures \subset(ArrayList.resultDep, \old(footprint));
      @   diverges true;
      @*/
    public /*@helper@*/ boolean contains(/*@nullable@*/ Object o) {
        //@ ghost \locset pcDep = \empty;
        //@ ghost \locset oDep = \empty;

        //@ ghost \locset iDep = pcDep; //assignment
        int i = 0;

        //@ set pcDep = \set_union(pcDep, \set_union(iDep, sizeDep)); //entering loop

        /*@ loop_invariant 0 <= i && i <= size
          @    && \subset(pcDep, \old(footprint))
          @    && \subset(iDep, \old(footprint));
          @ assignable \nothing;
          @ decreases size - i;
          @*/
        while(i < size) {
            //@ set pcDep = \set_union(pcDep, \set_union(arrayDep, \set_union(iDep, \set_union(oDep, arraySlotDep[i])))); //entering conditional
            if(array[i] == o) {
                //@ set ArrayList.resultDep = pcDep; //return
                return true;
            }

            //@ set iDep = \set_union(pcDep, iDep); //assignment
            i++;

            //@ set pcDep = \set_union(pcDep, \set_union(iDep, sizeDep)); //entering loop again
            ; //workaround for RecodeR bug
        }

        //@ set ArrayList.resultDep = pcDep; //return
        return false;
    }

    public /*@helper@*/ int size() {
        //@ ghost \locset pcDep = \empty;
        final int x;
        //@ set ArrayList.resultDep = \set_union(pcDep, sizeDep);
        return size;
    }

}
