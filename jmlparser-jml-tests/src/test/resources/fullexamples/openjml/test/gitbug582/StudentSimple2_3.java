package courseman.baderrs;

import java.util.ArrayList;
import java.util.List;

//@ model import org.jmlspecs.models.*;

/**
 * 
 * @overview 
 *
 * @author dmle
 *
 * @version
 * - ESC error: removeEnrolmentBad
 */
public class StudentSimple2_3 {
  
  private /*@ spec_public @*/ List enrolments;
  
  //////// CLASS INVARIANTS //////////////////////////
  /*@ 
    @  public invariant enrolments != null; // enrolments
    @*/
     
  /*@
    @   assignable \nothing;
    @   ensures
    @     enrolments != null && enrolments.isEmpty();  
    @*/
  public StudentSimple2_3() {
    enrolments = new ArrayList();
  }
  
  /*@
    @ requires e != null;
    @ ensures !\old(enrolments).contains(e) ==> 
    @            enrolments.equals(\old(enrolments).add(e));
    @*/
  public void addEnrolment(Object e) {
    if (!enrolments.contains(e))
      enrolments.add(e);
  }
  
  /*@
    @ requires e != null;
    @ ensures !enrolments.contains(e);
    @*/
  public void removeEnrolmentBad(Object e) {
    while (enrolments.contains(e)) // remove all
      enrolments.remove(e);
  }
  
  /*@
    @ requires e != null && enrolments.contains(e);
    @*/
  public void removeEnrolmentGood(Object e) {
    // do something
  }

}
