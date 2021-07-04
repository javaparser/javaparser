package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.StrongarmBase;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@Ignore // FIXME - Strongarm is broken - disabling tests
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class strongarm extends StrongarmBase {

    // @Override
    // public void setUp() throws Exception {
    //// noCollectDiagnostics = true;
    //// jmldebug = true;
    // super.setUp();
    // }

    public strongarm(String options, String solver) {
        super(options, solver);
    }

    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }

    public void helpSA(String sourceDirname, String outDir, String... opts) {
        onFile(sourceDirname, outDir, opts);
    }

    @Test
    public void testA() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A.java", "test/strongarm/base/");
    }

    @Test
    public void testA1() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A1.java", "test/strongarm/base/");
    }

    @Test
    public void testA2() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A2.java", "test/strongarm/base/");
    }
    @Test
    public void testA3() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A3.java", "test/strongarm/base/");
    }
    @Test
    public void testA4() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A4.java", "test/strongarm/base/");
    }
    @Test
    public void testA5() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A5.java", "test/strongarm/base/");
    }
    @Test
    public void testA6() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A6.java", "test/strongarm/base/");
    }
    @Test
    public void testA7() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A7.java", "test/strongarm/base/");
    }
    @Test
    public void testA8() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A8.java", "test/strongarm/base/");
    }
    @Test
    public void testA9() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A9.java", "test/strongarm/base/");
    }
    @Test
    public void testA10() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A10.java", "test/strongarm/base/");
    }
    @Test
    public void testA11() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A11.java", "test/strongarm/base/");
    }
    @Test
    public void testA12() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A12.java", "test/strongarm/base/");
    }
    @Test
    public void testA13() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A13.java", "test/strongarm/base/");
    }
    @Test
    public void testA14() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A14.java", "test/strongarm/base/");
    }

    @Test
    public void testA16b() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/A16.java", "test/strongarm/base/");
    }

    @Test
    public void testD() {
        //expectedExit = 1;
        helpSA("test/strongarm/base/D.java", "test/strongarm/base/");
    }

    @Test
    public void testS1() {
        helpSA("test/strongarm/base/S1.java", "test/strongarm/base/");
    }


    @Test
    public void testE1() {
        expectedExit = 0; 
        helpSA("test/strongarm/base/E1.java", "test/strongarm/base/");
    }

    /////// interprocedural tests

    @Test
    public void testA15() {
        //expectedExit = 1;
        helpSA("test/strongarm/interprocedural/A15.java", "test/strongarm/interprocedural/");
    }

    @Test
    public void testA16() {
        //expectedExit = 1;
        helpSA("test/strongarm/interprocedural/A16.java", "test/strongarm/interprocedural/");
    }


    @Test
    public void testA17() {
        //expectedExit = 1;
        helpSA("test/strongarm/interprocedural/A17.java", "test/strongarm/interprocedural/");
    }


    @Test
    public void testA18() {
        expectedExit = 1;
        helpSA("test/strongarm/interprocedural/A18.java", "test/strongarm/interprocedural/");
    }


    @Test
    public void testB() {
        //expectedExit = 1;
        helpSA("test/strongarm/interprocedural/B.java", "test/strongarm/interprocedural/");
    }



    //////// loop tests. 

    @Test
    public void testC1() {
        //expectedExit = 1;
        helpSA("test/strongarm/loops/C1.java", "test/strongarm/loops/");
    }


    /// examples



    @Test
    public void testDehexchar() {
        //expectedExit = 1;
        helpSA("test/strongarm/examples/Dehexchar.java", "test/strongarm/examples/");
    }

    @Test
    public void testEnd() {
        //expectedExit = 1;
        helpSA("test/strongarm/examples/End.java", "test/strongarm/examples/");
    }

    @Test
    public void testMore() {
        //expectedExit = 1;
        helpSA("test/strongarm/examples/More.java", "test/strongarm/examples/");
    }


    @Test
    public void testFeeeeeeilds() {
        //expectedExit = 1;
        helpSA("test/strongarm/examples/Feeeeeeilds.java", "test/strongarm/examples/");
    }


    @Test
    public void testStrangeResult() {
        //expectedExit = 1;
        helpSA("test/strongarm/examples/StrangeResult.java", "test/strongarm/examples/");
    }

    //    @Test
    //    public void testRowToString() {
    //	//expectedExit = 1;
    //	helpSA("test/strongarm/examples/RowToString.java", "test/strongarm/examples/");
    //    }

    //    @Test
    //    public void testNext() {
    //	//expectedExit = 1;
    //	helpSA("test/strongarm/examples/Next.java", "test/strongarm/examples/");
    //    }



}
