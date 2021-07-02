class C {
// demonstrates erreoneous termination

    /*@ normal_behavior
      @ ensures true;
      @ diverges true;
      @*/
    void foo () {
        assert false;
    }

    /*@ exceptional_behavior
      @ signals (Throwable) true;
      @ signals_only AssertionError;
      @*/
    void bar () {
        assert false;
    }

}
