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

final class A {

  public  byte m(long i) { return 2; }

  private int m(int i) { return 1; }

  static int callM() {
     A a = new A();
     return a.m(1);
  }

  static int callMviaB() {
     return B.callM();
  }

}

final class B {

  static int callM() {
     A a = new A();
     return a.m(1);
  }
}

public class Main {

  public static void main(){
      System.out.println(A.callM());
      System.out.println(B.callM());
      System.out.println(A.callMviaB());
  }
}
  

