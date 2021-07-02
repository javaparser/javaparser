class False {


   /*@ normal_behavior
     @ requires true;
     @ ensures false;
     @ diverges true;
     @ also
     @ exceptional_behavior
     @ requires true;
     @ signals (Exception) false;
     @ diverges true;
     @ helper
     @*/
   False () {}
}
