public class DoctorNurse {
  /*@ requires p instanceof Doctor
    @       || p instanceof Nurse; @*/
  public boolean isHead(final Staff p) {
    if (p instanceof Doctor) {
      Doctor doc = (Doctor) p;
      return doc.getTitle().startsWith("Head");
    } else {
      Nurse nrs = (Nurse) p;
      return nrs.isChief();
    }
  }
}
