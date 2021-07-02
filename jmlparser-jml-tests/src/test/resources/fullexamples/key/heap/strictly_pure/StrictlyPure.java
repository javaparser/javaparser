class StrictlyPure {

    int field;

    // We use the new keyword "\strictly_nothing" to specify
    // strict purity.

    /*@ requires true;
      @ assignable \strictly_nothing;
      @ ensures \result == field;
      @*/
    int strictlyPureMethod() {
	// assignable means modifies in KeY!
	// intermediate states may change the values of locations.
	
	field ++;
	field --;

	return field;
    }


    // new modifier: strictly_pure

    /*@ ensures \result == field; */
    /*@ strictly_pure*/ int strictlyPureModifierMethod() {
       return field;
    }

    /*@ requires field == 42;
      @ requires \invariant_for(o);
      @ ensures field == 42;
      @ ensures \dl_heap() == \old(\dl_heap());
      @ ensures \result == 0;
      @*/
    int useStrictlyPureMethod(StrictlyPureClass o) {
        o.thisMethodIsStrictlyPureByDefault();
	return strictlyPureMethod() - strictlyPureModifierMethod();
    }

    /* WARNING: If you use the line
     *  ensures \dl_heap() == \old(\dl_heap());
     *
     * in a specification of a contract, you are likely
     * to encounter an infinite loop when using the contract.
     * Rather use the equivalent and more powerful
     *  assignable \strictly_nothing;
     * or the modifier
     *  strictly_pure
     */
}
