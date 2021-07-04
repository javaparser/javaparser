package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfiles extends EscBase {

    boolean enableSubexpressions = false;
    
    public escfiles(String options, String solver) {
        super(options,solver);
    }
    
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
    	ignoreNotes = true;
    }
    
    public void helpTF(String testDirname, String ... opts) {
        String d = "test/" + testDirname;
        int extraOpts = 5;
        String[] newopts = new String[opts.length+extraOpts];
        // Fill in exactly 'extraOpts' initial elements
        newopts[0] = "-classpath";
        newopts[1] = d;
        newopts[2] = "-checkFeasibility=precondition,reachable,exit,spec";
        newopts[3] = "-code-math=bigint"; // Just to avoid overflow errors in these tests
        newopts[4] = "-spec-math=bigint"; // Just to avoid overflow errors in these tests
        System.arraycopy(opts,0,newopts,extraOpts,opts.length);
        helpTCF(d,d,newopts);
    }

    public void helpDemo(String testDirname, String outdir, String ... opts) {
        String d = OpenJMLDemoPath + "/src/openjml/" + testDirname;
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = d;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(d,"test/" + outdir,newopts);
    }

    public void helpTCA(String sourceDirname, String outDir, String ... opts) {
        int extraOpts = 5;
        String[] newopts = new String[opts.length+extraOpts];
        // Fill in exactly 'extraOpts' initial elements
        newopts[0] = "-classpath";
        newopts[1] = sourceDirname;
        newopts[2] = "-checkFeasibility=precondition,reachable,exit,spec";
        newopts[3] = "-code-math=bigint"; // Just to avoid overflow errors in these tests
        newopts[4] = "-spec-math=bigint"; // Just to avoid overflow errors in these tests
        System.arraycopy(opts,0,newopts,extraOpts,opts.length);
        escOnFiles(sourceDirname,outDir,newopts);
    }
    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        escOnFiles(sourceDirname,outDir,opts);
    }


    @Test
    public void testDemo() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClock.java","test/escDemo");
    }

    @Test
    public void testDemo1() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClock1.java","test/escDemo1","-escMaxWarnings=1");
    }

    @Test
    public void testDemoA() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockA.java","test/escDemoA","-subexpressions","-method=tick");
    }

    @Test
    public void testDemoA1() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockA1.java","test/escDemoA1","-subexpressions","-method=tick");
    }

    @Test
    public void testDemoB() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB.java","test/escDemoB");
    }

    @Test
    public void testDemoB1() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB1.java","test/escDemoB1",
                "-progress","-escMaxWarningsPath",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoB2() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB2.java","test/escDemoB2");
    }

    @Test
    public void testDemoB3() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB3.java","test/escDemoB3",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoC() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockC.java","test/escDemoC","-subexpressions");
    }

    @Test
    public void testDemoD() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockD.java","test/escDemoD","-subexpressions");
    }

    @Test
    public void testDemoTypes() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","-typeQuants=true","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "","-checkFeasibility=precondition,exit");
    }

    @Test // Problem with reasoning about generic types
    public void testDemoTypesAuto() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","-typeQuants=auto","-checkFeasibility=precondition,exit","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoTypesDef() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","-typeQuants=false","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "","-checkFeasibility=precondition,exit");
    }

    @Test // FIXME - Problem with int / short conversions
    public void testDemoTime() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Time.java","test/escDemoTime");
    }


    @Test // Order of errors is somewhat non-deterministic
    public void testBag() {
        expectedExit = 0;
        helpTCF("test/bag","test/bag","-escMaxWarnings=1");
    }

    @Test
    public void testBagModified() {
        expectedExit = 0;
        helpTCF("test/bagModified","test/bagModified");
    }

    @Test
    public void testLoopExercises() {
        expectedExit = 0;
        helpTCF("test/loopExercises","test/loopExercises","-exclude=gauss");
    }

    @Test @Ignore // FIXME - nonlinear inference
    public void testLoopExercises2() {
        expectedExit = 0;
        helpTCF("test/loopExercises","test/loopExercises","-method=gauss");
    }

    @Test @Ignore  // FIXME - not yet working
    public void testPurseCard() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/purse","test/purse","-timeout=15");
    }

    @Test @Ignore // FIXME - not yet working
    public void testPurseCardMod() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/purseMod","test/purseMod","-classpath",OpenJMLDemoPath + "/src/openjml/purseMod","-timeout=15");
    }

    @Test
    public void testTaxpayer() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Taxpayer.java","test/demoTaxpayer","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-checkFeasibility=precondition,exit");
    }

    @Test
    public void testBeanCan() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/BeanCan.java","test/demoBeancan","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-code-math=bigint","-spec-math=bigint","-checkFeasibility=precondition,exit");
    }

    @Test // Non-deterministic output
    public void testECU() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/ecudemo","test/ecuesc","-classpath",OpenJMLDemoPath + "/src/openjml/ecudemo","-escMaxWarnings=1");
    }

    @Test
    public void testValueTypes() {
        helpTF("valuetypes","-classpath","../OpenJML/runtime");
    }

    @Test
    public void testValueTypes2() {
        helpTF("valuetypes2","-classpath","../OpenJML/runtime");
    }

    @Test
    public void testValueTypesErr() {
        expectedExit = 1;
        helpTF("valuetypesErr","-classpath","../OpenJML/runtime");
    }

    @Test
    public void testOld() {
        helpTF("oldproblem","-classpath","../OpenJML/runtime");
    }

    @Test
    public void testFeasible() {
        helpTF("feasible");
    }

    // Just for debugging, not for testing
//    @Test
//    public void testOpt() {
//        helpTF("opt","-show","-method=m");
//    }

    @Test @Ignore // Problem is with mixed BV and bigint operations
    public void testBuggyCalculator() {
        helpTF("buggyCalculator");
    }

    @Test
    public void testBuggyRandomNumbers() {
        helpTF("buggyRandomNumbers");
    }

    @Test @Ignore // times out -- see testPrime for fixed version
    public void testPrimeNumbers() {
        helpTF("buggyPrimeNumbers");
    }

    @Test @Ignore // FIXME - unclear why fails
    public void testBuggyPalindrome() {
        helpTF("buggyPalindrome");
    }

    @Test
    public void testException() {
        helpTF("escException");
    }

    @Test
    public void testPreOld() {
        helpTF("preold");
    }

    @Test
    public void testPreOld2() {
        expectedExit = 1;
        helpTF("preold2");
    }

    @Test
    public void testNullableOld() {
        helpTF("nullableOld");
    }

    @Test
    public void testStaticOld() {
        expectedExit = 1;
        helpTF("staticOld");
    }

    @Test
    public void testINF() {
        helpTF("escINF");
    }

    @Test
    public void testAdd() {
        expectedExit = 1;
        helpTF("escAdd");
    }

    @Test
    public void testAdd2() {
        expectedExit = 0;
        helpTF("escAdd2");
    }

    @Test
    public void testArrayCopy() {
        expectedExit = 0;
        helpTF("escArrayCopy");
    }

    @Test
    public void testArrayClone() {
        expectedExit = 0;
        helpTF("escClone");
    }
    @Test
    public void test2DArray() {
        expectedExit = 0;
        helpTF("esc2DArray");
    }

    @Test @Ignore // FIXME - axioms for multi-dimensional arrays
    public void test2DTranspose() {
        expectedExit = 0;
        helpTF("esc2DTranspose");
    }

    @Test @Ignore // FIXME - Specs need improvement
    public void testVT20191() {
        expectedExit = 0;
        helpTF("verifythis-2019-1","-checkFeasibility=none"); // FIXME - feasibility check times out
    }

    @Test
    public void testVT20192() {
        expectedExit = 0;
        helpTF("verifythis-2019-2","-solver-seed=42");
    }

    @Test 
    public void testCashAmount() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmount.java","test/escCashAmount","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-escMaxWarnings=1");
    }

    @Test
    public void testCashAmount2() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountOnlyPrivate.java","test/escCashAmountonlyPrivate","-classpath",OpenJMLDemoPath + "/src/openjml/demo");
    }

    @Test
    public void testCashAmountMutable() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountMutable.java","test/escCashAmountMutable","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-code-math=bigint","-spec-math=bigint");
    }

    @Test
    public void testCashAmountMF() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountMF.java","test/escCashAmountMF","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-escMaxWarnings=1");
    }

    @Test
    public void testSettableClock() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpDemo("settableClock","escSettableClock");
    }

    @Test
    public void testVector() {
        expectedExit = 0;
        helpTF("escVector","-code-math=java");
    }

    @Test
    public void testDMZLoop() {
        expectedExit = 0;
        helpTF("escDMZLoop","-method=findMax");
    }

    @Test
    public void testDMZLoopA() {
        expectedExit = 0;
        helpTF("escDMZLoopA","-method=findMax","-code-math=bigint","-spec-math=bigint");
    }

    @Test
    public void testDMZLoopB() {
        expectedExit = 0;
        helpTF("escDMZLoopB","-method=findMax","-code-math=bigint","-spec-math=bigint");
    }

    @Test
    public void testRecursiveInvariant() {
        expectedExit = -1;
        helpTF("escRecursiveInvariant");
    }

    @Test
    public void testRecursiveInvariant2() {
        expectedExit = -1;
        helpTF("escRecursiveInvariant2");
    }

    @Test
    public void testquant() {
        expectedExit = -1;
        helpTF("testquant");
    }

    @Test
    public void testConstructorDefaults() {
        expectedExit = 0;
        helpTF("constructorDefaults");
    }

    @Test
    public void testInlinedLoop() {
        expectedExit = 0;
        helpTF("escInlineLoop");
    }


    // FIXME - reasoning about getClass
    @Test
    public void testBadCast() {
        expectedExit = 0;
        helpTF("escBadCast");
    }

    @Test
    public void testCashAmountPrivate2() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF("test/escCashAmountPrivate2/CashAmountOnlyPrivate.java","test/escCashAmountPrivate2","-classpath","test/escCashAmountPrivate2","-method=increase");
    }

    @Test
    public void testJLS() {
        expectedExit = 0;
        helpTF("escJLS");
    }

    @Test
    public void testDoublyLinkedList() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTF("escDoublyLinkedList");
    }

    @Test
    public void testEscModelFields() {
        helpTF("escModelFields","-progress");
    }

    @Test
    public void testEscSimpleString() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver)); // FIXME - CVC4 crashes or is long
        helpTF("escSimpleString","-nonnullByDefault","-timeout=240");
    }

    @Test
    public void testEscSimpleString2() {
        helpTF("escSimpleString2","-nonnullByDefault");
    }

    @Test
    public void testEscSimpleString3() {
        helpTF("escSimpleString3","-nonnullByDefault");
    }


    @Test @Ignore // FIXME - implement diverges
    public void testEscDiverges() {
        helpTF("escDiverges","-nonnullByDefault");
    }


    @Test
    public void testEscDiverges2() {
        helpTF("escDiverges2","-nonnullByDefault");
    }
    
    @Test @Ignore // FIXME - string comparisons for switch statements
    public void escStrings() {
        helpTF("escStrings");
    }
    
    @Test
    public void escEnum() {
        helpTF("escEnum");
    }
    
    @Test
    public void testEscLoop() {
        helpTF("escLoop");
    }

    @Test
    public void testEscLoopModifies() {
        helpTF("escLoopModifies");
    }

    @Test
    public void testEscLoopAssignable() {
        expectedExit = 1;
        helpTF("escLoopAssignable");
    }

    @Test
    public void testEscBodySpecs() {
        helpTF("escBodySpecs");
    }

    @Test
    public void testEscDeterministic() {
        helpTF("escDeterministic");
    }

    @Test
    public void testEscDeterministic2() {
        helpTF("escDeterministic2");
	}

    @Test
    public void testEscFunction() {
        helpTF("escFunction");
    }
    
    @Test
    public void testAbstractSpecs() {
        helpTF("escAbstractSpecs");
    }
    
    @Test
    public void testAbstractSpecs2() {
    	expectedExit = 1;
        helpTF("escAbstractSpecs2");
    }
    
    @Test
    public void testEscInvariants() {
        helpTF("escInvariants");
    }

    @Test
    public void testEscInvariants2() {
        helpTF("escInvariants2");
    }

    @Test
    public void testJmlSpecPublic() {
        helpTCF("test/escSeparateJml/BankingExample.java","test/escSeparateJml","-classpath","test/escSeparateJml");
    }

    @Test
    public void escDouble() {
        helpTF("escDouble");
    }

    @Test
    public void escDouble2() {
        helpTF("escDouble2","-exclude=clone,remainderBy,toString,approximatelyEqualTo");
    }

    @Test @Ignore
    public void escDouble2a() {
        helpTF("escDouble2","-escMaxWarnings=1","-show","-method=remainderBy","-subexpressions");
    }

    @Test
    public void escDouble2b() {
        helpTF("escDouble2b","-method=approximatelyEqualTo");
    }

    @Test
    public void escDoubleArith() {
        helpTF("escDoubleArith");
    }

   @Test
    public void escAssignableBug() {
        helpTF("escAssignableBug");
    }

    @Test
    public void escDerivedInvariant() {
        helpTF("escDerivedInvariant");
    }

    @Test
    public void testEscConstructor() {
        helpTF("escConstructor");
    }

    @Test
    public void testEscConstructor2() {
        helpTF("escConstructor2");
    }

    @Test
    public void testEscConstructor3() {
        helpTF("escConstructor3");
    }

    @Test
    public void testEscConstructor4() {
        helpTF("escConstructor4");
    }
    
    @Test
    public void testEscConstructor5() {
        helpTF("escConstructor5");
    }

    @Test
    public void testEscConstructor6() {
        helpTF("escConstructor6");
    }

    @Test
    public void testEscShortCircuit() {
        helpTF("escShortCircuit");
    }
    
    @Test
    public void testEscRecursiveOld() {
        helpTF("escRecursiveOld");
    }
    
    @Test
    public void testEnsuresInfeasible() {
        helpTF("escEnsuresInfeasible");
    }

    @Test
    public void testEnsuresInfeasible2() {
        helpTF("escEnsuresInfeasible2");
    }

    @Test
    public void testConstructorInfeasible() {
        helpTF("escConsInfeasible");
    }

    @Test
    public void testEscMultipleModel() {
        helpTF("escMultipleModel");
    }

    @Test
    public void testEscMultipleModel2() {
        helpTF("escMultipleModel2");
    }

    @Test
    public void testEscMultipleModel3() {
        helpTF("escMultipleModel3");
    }

    @Test
    public void testPreconditionDetail() {  // FIXME - why multiple conjuncts reported
        helpTF("preconditionDetail");
    }

    @Test // FIXME - still has problems with imports in JML files and with checks on field initializers
    public void testEscJml() {
        helpTCF("test/escJML/Test.java","test/escJML","-specspath=test/escJML/specs");
    }

    @Test
    public void testEscJml1() {
        helpTCF("test/escJml1/StorageParameters.java","test/escJml1","-specspath=test/escJml1/specs");
    }

    @Test
    public void testEscJml2() {
        helpTCF("test/escJml2/StorageParameters.java","test/escJml2","-specspath=test/escJml2/specs");
    }

    @Test
    public void testEscJml3() {
        helpTCF("test/escJml3/StorageParameters.java","test/escJml3","-specspath=test/escJml2/specs");
    }

    @Test
    public void testEscJmlDup() {
        helpTF("escDup");
    }

    @Test
    public void escLet() {
        helpTF("escLet","-solver-seed=9999");
    }
    
    @Test
    public void escElse() {
        helpTF("Else");
    }

    @Test
    public void escConsFresh() {
        helpTF("consfresh");
    }

    @Test
    public void testSpecificationInterface() {
        helpTF("specificationInterfaceDemo");
    }

    @Test
    public void testImplicitIteration() {
        helpTF("implicitIteration");
    }

    @Test
    public void testImplicitIterationA() {
        helpTF("implicitIterationA");
    }

    // The following are split into multiple tests to minimize the combinatorial non-determinism in the output
    @Test
    public void testEscSF420() {
        helpTF("sfbug420","-exclude=count;itemAt;main;isEmpty;push;top");
    }
    
    @Test
    public void testEscSF420a() {
        helpTF("sfbug420a","-method=count");
    }
    
    @Test
    public void testEscSF420b() {
        helpTF("sfbug420b","-method=itemAt");
    }
    
    @Test
    public void testEscSF420c() {
        helpTF("sfbug420c","-method=main");
    }
    
    @Test
    public void testEscSF420d() {
        helpTF("sfbug420d","-method=isEmpty");
    }
    
    @Test
    public void testEscSF420e() {
        helpTF("sfbug420e","-method=push");
    }
    
    @Test
    public void testEscSF420f() {
        helpTF("sfbug420f","-method=top");
    }
    
    @Test
    public void testEscSF420X() {
        helpTF("sfbug420X");
    }
    
    @Test  // TODO - could use some additional investigation as to what this submitted file set is supposed to do
    public void testRmLoop() {
        helpTF("escrmloop","-checkFeasibility=none","-timeout=60");
    }
    
    @Test
    public void testRmLoop2() {
        expectedExit = 1;
        helpTF("escrmloop2");
    }
    
    @Test @Ignore // not working yet
    public void escFPcompose() {
        helpTF("escFPcompose");
    }
    
    @Test
    public void escLemma() {
        helpTF("escLemma");
    }
    
    @Test
    public void escOld() {
        helpTF("escOld");
    }
    
    @Test
    public void exceptionCancel() {
        helpTF("exceptionCancel");
    }
    

    
    @Test @Ignore // FIXME - ignore for now; implement with real specs
    public void testEscRawding() {
        helpTF("escRawding","-specspath=test/escRawding","-code-math=safe");
    }
    
    // The following are really just typecheck problems

    @Test
    public void testEscPrivate() {
        expectedExit = 0;
        helpTF("escPrivate");
    }

    @Test  // FIXME - not yet working
    public void testPrimitiveTypes() {
        expectedExit = 0;
        helpTF("primitives");
    }

    @Test
    public void testEnums() {
        expectedExit = 0;
        helpTF("enums");
    }

    @Test @Ignore // FIXME - not yet implemented
    public void testEnums1() {
        expectedExit = 0;
        helpTF("enums1");
        //helpTF("enums1","-show","-method=m5c","-subexpressions");
    }

    @Test
    public void testEnums2() {
        expectedExit = 0;
        helpTF("enums2");
    }

    @Test
    public void testDatatypes() {
        expectedExit = 0;
        helpTF("datatype");
    }

    @Test // Basic problem is with the toString conversion of a \bigint, because of the -code-math=bigint setting of these
    public void testFactorial() {
        expectedExit = 0;
        helpTF("factorial");//,"-code-math=java");
    }

    @Test @Ignore // FIXME - times out
    public void testPrime() {
        expectedExit = 0;
        helpTF("primeNumbers");
    }
    
    @Test
    public void testSplits() {
        expectedExit = 0;
        helpTF("splits");
    }
    
    @Test
    public void testSplits2() {
        expectedExit = 0;
        helpTF("splits2");
    }
    
    @Test
    public void Dzmz() {
        expectedExit = 0;
        helpTF("Dzmz");
    }

    @Test
    public void refining() {
        expectedExit = 0;
        helpTF("refining");
    }

    @Test
    public void refiningBad() {
        expectedExit = 1;
        helpTF("refiningBad");
    }

    @Test @Ignore // FIXME - fix a problem with concatenation
    public void testGCDCalculator() {
        expectedExit = 0;
        helpTF("gcdcalculator");
    }

    @Test
    public void testEscVisibilitySimple() {
        expectedExit = 1;
        helpTF("visibilitySimple");
    }

    @Test
    public void testVisibilityB() {
        expectedExit = 1;
        helpTCF("test/visibilityB/org/apache/commons/cli/Option.java","test/visibilityB","-classpath","test/visibilityB");
    }

    @Test
    public void testRequiresElse() { // FIXME - why the two different formats of output
        helpTF("requiresElse","-show=program"); // -show=program is part of test results
    }

    @Test
    public void testTuple() {
        helpTF("tuple");
    }

    @Test
    public void testTupleBad() {
        expectedExit = 1;
        helpTF("tupleBad");
    }

    @Test @Ignore // FIXME - not yet implemented
    public void testCaptures() {
        expectedExit = 1;
        helpTF("anonymousCaptures");
    }
    
    @Test @Ignore // FIXME - needs implementation
    public void testStreams() {
        expectedExit = 1;
        helpTF("streams");
    }
    
    @Test
    public void checkAsserts() {
        helpTF("checkAsserts");
    }
    
    @Test
    public void callstacks() {
        helpTF("callstacks");
    }
    
    @Test
    public void varargs() {
        helpTF("varargs");
    }
    
    @Test
    public void jmlstring() {
        helpTF("valuestrings");
    }
    
    @Test
    public void jmlstringBad() {
        expectedExit = 1;
        helpTF("valuestringsBad");
    }
    
    @Test // FIXME - get an infeasibility when Arrays.binarySearch uses Arrays.contains
    public void binarySearch() {
        helpTF("binarySearch");
    }


}
