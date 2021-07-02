// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/** A larger scale enum declaration and a method using a switch statement over
 * this enum. enum_large.key uses these sources.
 */
 

enum Large {

  large1, large2, large3, large4, large5, large6, large7, large8, large9, large10, 
  large11, large12, large13, large14, large15, large16, large17, large18, large19,
  large20, large21, large22, large23, large24, large25, large26, large27, large28,
  large29, large30, large31, large32, large33, large34, large35, large36, large37,
  large38, large39, large40, large41, large42, large43, large44, large45, large46,
  large47, large48, large49, large50; 


  public static int m(Large l) {

     switch(l) {
         case large1: return 1;
         case large2: return 2;
         case large3: return 3;
         case large4: return 4;
         case large5: return 5;
         case large6: return 6;
         case large7: return 7;
         case large8: return 8;
         case large9: return 9;
         case large10: return 10;
         case large11: return 11;
         case large12: return 12;
         case large13: return 13;
         case large14: return 14;
         case large15: return 15;
         case large16: return 16;
         case large17: return 17;
         case large18: return 18;
         case large19: return 19;
         case large20: return 20;
         case large21: return 21;
         case large22: return 22;
         case large23: return 23;
         case large24: return 24;
         case large25: return 25;
         case large26: return 26;
         case large27: return 27;
         case large28: return 28;
         case large29: return 29;
         case large30: return 30;
         case large31: return 31;
         case large32: return 32;
         case large33: return 33;
         case large34: return 34;
         case large35: return 35;
         case large36: return 36;
         case large37: return 37;
         case large38: return 38;
         case large39: return 39;
         case large40: return 40;
         case large41: return 41;
         case large42: return 42;
         case large43: return 43;
         case large44: return 44;
         case large45: return 45;
         case large46: return 46;
         case large47: return 47;
         case large48: return 48;
         case large49: return 49;
         case large50: return 50;
    }
    throw new Error();
  }
}
