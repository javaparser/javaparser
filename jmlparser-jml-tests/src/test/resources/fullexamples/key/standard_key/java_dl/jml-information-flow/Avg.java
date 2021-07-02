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

/**
 * Example by Guillaume Dufay about specification of
 * security/non-interference properties using JML.
 */

 public class Avg {
 
     //@ public invariant TAG_ATTR_IDX == 0;
     public static final int TAG_ATTR_IDX = 0;
 
     //@ public invariant VALUE_ATTR_IDX == 1;
     public static final int VALUE_ATTR_IDX = 1;
 
     public int [][] m_Tab;
     public int [][] m_Tab2;
 
     // public ghost int [] m_Sum;
     //@ public invariant m_Sum != null;
     private int [] m_Sum;
 
     //@ public invariant num_Instances >= 1;
     public int num_Instances;
 
     //@ public invariant num_Attributes >= 2;
     public int num_Attributes;
 
     public int res1, res2;
 
 
    // Original code
     public int average_ori() {
       int result = 0;
       int total = 0;
 
       for (int i = 0 ; i < num_Instances ; i++) {
           if (m_Tab[i][TAG_ATTR_IDX] != 0) {
               result += m_Tab[i][VALUE_ATTR_IDX];
               total += 1;
           }
       }
       if (total != 0)
           result /= total;
 
       return result;
     }
 
     // Code modified for self-composition
     /*@
       @ public normal_behavior
       @ requires m_Tab != null && m_Tab.length == num_Instances &&
       @   m_Tab2 != null && m_Tab2.length == num_Instances &&
       @   (\forall int i; 0 <= i && i < num_Instances;
       @      m_Tab[i] != null && m_Tab[i] instanceof int[] &&
       @      m_Tab[i].length == num_Attributes) &&
       @   (\forall int i; 0 <= i && i < num_Instances;
       @      m_Tab2[i] != null && m_Tab2[i] instanceof int[] &&
       @      m_Tab2[i].length == num_Attributes) &&
       @   m_Sum.length == num_Instances+1 &&
       @   (\forall int i; 0 <= i && i < num_Instances;
       @     m_Sum != m_Tab[i] && m_Sum != m_Tab2[i]) &&
       @
       @  (\forall int i; 0 <= i && i < num_Instances;
       @   m_Tab[i][TAG_ATTR_IDX] == m_Tab2[i][TAG_ATTR_IDX]) &&
       @  (\forall int i; 0 <= i && i < num_Instances;
       @    ((m_Tab[i][TAG_ATTR_IDX] != 0) ==>
       @      (m_Tab[i][VALUE_ATTR_IDX] == m_Tab2[i][VALUE_ATTR_IDX])));
       @ modifiable res1, res2, m_Sum[*];
       @ ensures res1 == res2;
       @*/
 
     public void average() {
       int total1 = 0, total2 = 0;
 
       m_Sum[0] = 0;
 
       res1 = 0;
       { int i = 0;
       /*@ loop_invariant
       @ 0 <= i && i <= num_Instances && m_Sum[0] == 0 &&
       @ (\forall int j; 0 < j && j <= i;
       @  ((m_Tab[j-1][TAG_ATTR_IDX] == 0) ==> (m_Sum[j] == m_Sum[j-1])) &&
       @  ((m_Tab[j-1][TAG_ATTR_IDX] != 0) ==>
       @      (m_Sum[j] == m_Sum[j-1] + m_Tab[j-1][VALUE_ATTR_IDX]))) &&
       @  res1 == m_Sum[i];
       @ decreases num_Instances - i;
       @ modifies m_Sum[*], res1;
       @*/
       while ( i < num_Instances ) {
           if (m_Tab[i][TAG_ATTR_IDX] != 0) {
               res1 += m_Tab[i][VALUE_ATTR_IDX];
               total1 += 1;
               // Should be ghost variables,
               // but incorrectly handled by Krakatoa
               // SET m_Sum[i+1] = m_Sum[i] + m_Tab[i][VALUE_ATTR_IDX];
               m_Sum[i+1] = m_Sum[i] + m_Tab[i][VALUE_ATTR_IDX];
           } else {
               // SET m_Sum[i+1] = m_Sum[i];
               m_Sum[i+1] = m_Sum[i];
           }
	   i++;
       }
       }
       //      if (total1 != 0)
       //          res1 /= total1;
 
       res2 = 0;
       { int i = 0;
       /*@ loop_invariant
       @ 0 <= i && i <= num_Instances &&
       @  res2 == m_Sum[i];
       @ decreases num_Instances - i;
       @ modifies res2;
       @*/
       while ( i < num_Instances ) {
           if (m_Tab2[i][TAG_ATTR_IDX] != 0) {
               res2 += m_Tab2[i][VALUE_ATTR_IDX];
               total2 += 1;
           }
	   i++;
       }
       }
       //      if (total2 != 0)
       //          res2 /= total2;
     }
 }
 
