public class Else {

public boolean AA,BB,CC,DD,EE;


//@   requires BB;
//@   requires CC;
//@   ensures \result == true;
//@ also
//@   requires DD;
//@   requires EE;
//@   ensures \result == true;
//@ also
//@   requires \else;
//@   ensures \result == false;
//@ pure
public boolean m() {
    if (BB && CC) return true;
    if (DD && EE) return true;
    return false;

  }

//@ requires m();
//@ ensures \result == true;
public boolean m2() {
    if (BB && CC) return true;
    if (DD && EE) return true;
    //@ unreachable;
    return false;

  }


//@ requires AA;
//@ {|
//@   requires BB;
//@   requires CC;
//@   ensures \result == true;
//@ also
//@   requires DD;
//@   requires EE;
//@   ensures \result == true;
//@ also
//@   requires \else;
//@   ensures \result == false;
//@ |}

public boolean mm() {
  if (AA && BB && CC) return true;
  if (AA && DD && EE) return true;
  return false;

}

}
