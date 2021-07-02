public class AuxiliaryContractsFinally {

  int i;

  /*@ requires e != null;
    @ ensures i == 2;
    @ diverges true; @*/
  void breakThrowContinueLoopContract(Exception e) {
    i = 1;
    /*@ loop_contract normal_behavior
	@ requires i == 1;
	@ ensures i == 2;
	@*/
    while (i < 3) {
      i++;
      try {
        try {
          break;
        } finally {
          throw e;
        }
      } catch (Exception ex) {
        continue;
      }
    }
  }

  void breakThrowContinueBlockContract(Exception e) {
    /*@
	@ returns true;
	@ ensures false;
	@*/
	{
      try {
        try {
          return;
        } finally {
          throw e;
        }
      } catch (Exception ex) {
        try {
          try {
            return;
          } finally {
            throw e;
          }
        } catch (Exception ex2
        ) {
          // terminate normally
        }
      }
    }
  }

}
