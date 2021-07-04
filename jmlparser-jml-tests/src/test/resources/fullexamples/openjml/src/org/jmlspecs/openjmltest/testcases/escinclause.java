package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escinclause extends EscBase {

    public escinclause(String options, String solver) {
        super(options,solver);
    }
        
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //main.addOptions("-jmlverbose");
        //main.addOptions("-method",   "m2bad");
        //main.addOptions("-jmldebug");
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    @Test
    public void testInClause1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ model public int mx;\n"
                +"  int x; //@ in mx; \n"
                +"  int y;\n"

                +"  //@ assignable mx; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable mx; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  y",7
                ,"/tt/TestJava.java:6: warning: Associated declaration",7
                );
    }

}
