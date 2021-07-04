package org.jmlspecs.openjmltest.testcases;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SFBugs extends EscBase {
    
    String cpathAddition = "";

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        ignoreNotes = true;
    }

    public SFBugs(String options, String solver) {
        super(options, solver);
    }
    
    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }
    
    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        //Assert.fail(); // FIXME - Java8 - long running
        ArrayList<String> list = new ArrayList<String>();
        list.add("-code-math=safe");
        list.add("-spec-math=bigint");
        list.addAll(Arrays.asList(opts));
        escOnFiles(sourceDirname,outDir,list.toArray(opts));
    }

    public void helpTCG(String ... opts) {
        String dir = "test/" + getMethodName(1);
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir + cpathAddition);
        a.add("-code-math=safe");
        a.add("-spec-math=bigint");
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }

    public void helpTCGNoOptions(String ... opts) {
        String dir = "test/" + getMethodName(1);
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir + cpathAddition);
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }



    @Test public void typecheckWithJML() {
        expectedExit = 1;
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml", "-check");
    }
    
    @Test public void sfpatch25() {
        helpTCF("test/sfpatch25/A.java","test/sfpatch25", "-cp", "test/sfpatch25", "-esc","-quiet");
    }
    
    @Test public void sfbug407() {
        helpTCF("test/sfbug407","test/sfbug407", "-cp", "test/sfbug407", "-esc", "-progress");
    }
    
    @Test public void sfbug398() {
        helpTCF("test/sfbug398","test/sfbug398", "-cp", "test/sfbug398", "-esc", "-progress");
    }
    
    @Test public void sfbug399() {
        helpTCF("test/sfbug399","test/sfbug399", "-cp", "test/sfbug399", "-esc","-progress");
    }
    
    @Test public void sfbug404() {
        helpTCF("test/sfbug404","test/sfbug404", "-cp", "test/sfbug404", "-esc","-progress","-logic=AUFNIRA");
    }
    
    @Test public void sfbug408() {
        helpTCF("test/sfbug408","test/sfbug408", "-cp", "test/sfbug408", "-esc","-progress");
    }
    
    @Test public void sfbug409() {
        helpTCF("test/sfbug409","test/sfbug409", "-cp", "test/sfbug409", "-esc","-progress");
    }
    
    @Test public void sfbug410() {
        helpTCF("test/sfbug410","test/sfbug410", "-cp", "test/sfbug410", "-esc","-progress");
    }
    
    @Test public void sfbug414() {
        expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "-esc","-progress","-logic=AUFNIRA","-escMaxWarnings=5");
    }

    @Test public void gitbug257() {
        expectedExit = 0;
        helpTCF("test/gitbug257","test/gitbug257", "-cp", "test/gitbug257", "-esc", "-progress", "-logic=AUFNIRA");
    }
    
    @Test public void gitbug260() {
        expectedExit = 0;
        helpTCF("test/gitbug260","test/gitbug260", "-cp", "test/gitbug260", "-esc", "-progress");
    }
    
    @Test public void gitbug431() {
        expectedExit = 0;
        helpTCF("test/gitbug431","test/gitbug431", "-cp", "test/gitbug431", "-esc", "-progress");
    }
    
    @Test public void gitbug450() {
        expectedExit = 1;
        ignoreNotes = true;
        helpTCF("test/gitbug450","test/gitbug450", "-cp", "test/gitbug450", "-esc", "-progress");
    }
    
    @Test public void gitbug450c() {
        expectedExit = 0;
        helpTCF("test/gitbug450c","test/gitbug450c", "-cp", "test/gitbug450c", "-esc", "-progress");
    }
    
    @Test public void gitbug454() {
        expectedExit = 0;
        helpTCF("test/gitbug454","test/gitbug454", "-cp", "test/gitbug454", "-esc");
    }
    
    @Test public void gitbug457() {
        expectedExit = 0;
        helpTCG("-nullableByDefault");
    }
    
    @Test public void gitbug457a() {
        expectedExit = 0;
        helpTCG("-nonnullByDefault");
    }
    
    @Test public void gitbug458() {
        expectedExit = 0;
        helpTCF("test/gitbug458","test/gitbug458", "-cp", "test/gitbug458", "-esc");
    }
    
    @Test public void gitbug458a() {
        expectedExit = 0;
        helpTCF("test/gitbug458a","test/gitbug458a", "-cp", "test/gitbug458a", "-esc");
    }
    
    @Test public void gitbug458b() {
        expectedExit = 0;
        helpTCF("test/gitbug458b","test/gitbug458b", "-cp", "test/gitbug458b", "-esc");
    }
    
    @Test public void gitbug459() {
        expectedExit = 0;
        helpTCF("test/gitbug459","test/gitbug459", "-cp", "test/gitbug459", "-esc");
    }
    
    @Test public void gitbug461() {
        expectedExit = 0;
    }
    
    @Test public void gitbug462() {
        expectedExit = 0;
        helpTCF("test/gitbug462","test/gitbug462", "-cp", "test/gitbug462", "-esc");
    }
    
    @Test public void gitbug462a() {
        expectedExit = 0;
        helpTCF("test/gitbug462a","test/gitbug462a", "-cp", "test/gitbug462a", "-esc");
    }
    
    @Test public void gitbug462b() {
        expectedExit = 0;
        helpTCF("test/gitbug462b","test/gitbug462b", "-cp", "test/gitbug462b", "-esc");
    }
    
    @Test public void gitbug462c() {
        expectedExit = 0;
        helpTCF("test/gitbug462c","test/gitbug462c", "-cp", "test/gitbug462c", "-esc");
    }
    
    @Test public void gitbug456() {
        expectedExit = 0;
        helpTCF("test/gitbug456","test/gitbug456", "-cp", "test/gitbug456", "-esc", "-exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug456a() {
        expectedExit = 0;
        helpTCF("test/gitbug456a","test/gitbug456a", "-cp", "test/gitbug456a", "-esc", "-exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug455() {
        expectedExit = 0;
        helpTCF("test/gitbug455","test/gitbug455", "-cp", "test/gitbug455", "-esc");
    }
    
    @Ignore // FIXME - needs ability to specify/reason about derived classes
    @Test public void gitbug446() {
        expectedExit = 0;
        helpTCF("test/gitbug446","test/gitbug446", "-cp", "test/gitbug446", "-esc");
    }
    
    @Ignore // FIXME - syntax for model programs not settled
    @Test public void gitbug445() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Ignore // FIXME - syntax for model programs not settled
    @Test public void gitbug445a() {
        helpTCG();
    }
    
    @Test public void gitbug463() {
        expectedExit = 0;
        helpTCF("test/gitbug463","test/gitbug463", "-cp", "test/gitbug463");
    }
    
    @Test public void gitbug463a() {
        expectedExit = 0;
        helpTCF("test/gitbug463a","test/gitbug463a", "-cp", "test/gitbug463a");
    }
    
    @Test public void gitbug444() {
        expectedExit = 0;
        helpTCF("test/gitbug444","test/gitbug444", "-cp", "test/gitbug444");
    }
    
    @Test public void gitbug444a() {
        expectedExit = 0;
        helpTCF("test/gitbug444a","test/gitbug444a", "-cp", "test/gitbug444a");
    }

    @Test public void gitbug466() {
        expectedExit = 0;
        helpTCF("test/gitbug466","test/gitbug466", "-cp", "test/gitbug466","-method=Test.run");
    }

    @Test public void gitbug467() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug470() {
        expectedExit = 0;
        helpTCF("test/gitbug470/ACD.java","test/gitbug470", "-cp", "test/gitbug470","-code-math=java");
    }

    @Test public void gitbug471() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug469() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug474() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug476() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug477() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug478() {
        expectedExit = 0;
        helpTCG();  // NOTE: Uses a custom instance of ByteBuffer.jml, which made the original bug
    }

    @Test public void gitbug480() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug497() {
        expectedExit = 1;
        helpTCG();
    }

    @Test public void gitbug498() {
        expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug499() {
        expectedExit = 1;
        helpTCG();
    }

    @Ignore // FIXME - times out
    @Test public void gitbug500a() {
        helpTCG("-solver-seed=242");
    }

    @Ignore // FIXME - times out
    @Test public void gitbug500b() {
        helpTCG("-solver-seed=242");
    }

    @Test public void gitbug500c() {
        helpTCG("-rac");  // Just RAC compilation - RAC compile crash
    }

    @Test public void gitbug502() {
        helpTCG();
    }

    // FIXME - problem in 503 is that various subtests non-deterministically timeout
    // This seems particularly the case with A1 and A4, which have an extraneous template argument
    @Ignore // times out
    @Test public void gitbug503() {
        helpTCG("-code-math=java","-timeout=600","-solver-seed=142"); // java math just to avoid overflow error messages
    }

    @Ignore // times out
    @Test public void gitbug503a() {
        helpTCG("-code-math=java","-timeout=600","-solver-seed=42"); // java math just to avoid overflow error messages
    }

    @Test public void gitbug535() {
        helpTCG();
    }

    @Test public void gitbug538() {
        helpTCG();
    }

    @Test public void gitbug539() {
        helpTCG();
    }

    @Test public void gitbug540() {
        helpTCG();
    }

    @Test public void gitbug543() {
        helpTCG();  // FIXME - demonstrates problems with quantification over arrays
    }

    @Test public void gitbug545() {
        helpTCG();
    }

    @Test public void gitbug548() {
        helpTCG("-nullableByDefault");
    }
    
    @Test public void gitbug550() {
        helpTCG();
    }
    
    @Test public void gitbug554() {
        helpTCG();
    }
    
    @Test public void gitbug555() {
        helpTCG("-nullableByDefault");
    }
    


    @Test public void gitbug518() {
        expectedExit = 1;
        helpTCG("-check");  // Just checking
    }

    @Test public void gitbug528() {
        helpTCG("-lang=jml","-check");  // Just checking
    }

    @Test public void gitbug529() {
        helpTCG("-rac");  // Just RAC compilation  // FIXME - try running also
    }

    // Check everything in apache commons library!
    // FIXME - Needs more specification to avoid the errors reported in the tests below

    @Ignore // This checks everything - which times out - so the verification is broken up in other tests
    @Test public void gitbug481() {
        expectedExit = 0;
        helpTCF("test/gitbug481b","test/gitbug481", "-cp", "test/gitbug481b","-progress");
    }

    // Just one method, but parse and typecheck all files first
    @Test public void gitbug481c() {
        expectedExit = 0;
        helpTCF("test/gitbug481b","test/gitbug481c", "-cp", "test/gitbug481b","-method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry");
    }

    // Just one method in one file
    @Test public void gitbug481b() {
        expectedExit = 0;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481b", "-cp", "test/gitbug481b","-method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry","-no-staticInitWarning");
    }

    static String p = "org.apache.commons.math3.linear.ArrayFieldVector.";
    static String m1 = p + "ArrayFieldVector(org.apache.commons.math3.Field<T>)";
    static String m2 = p + "ArrayFieldVector(org.apache.commons.math3.Field<T>,int)";
    static String m3 = p + "ArrayFieldVector(int,T)";
    static String m4 = p + "ArrayFieldVector(org.apache.commons.math3.linear.ArrayFieldVector<T>,boolean)";
    static String m5 = p + "ArrayFieldVector(org.apache.commons.math3.linear.ArrayFieldVector<T>,org.apache.commons.math3.linear.ArrayFieldVector<T>)";
    static String m6 = p + "ArrayFieldVector(org.apache.commons.math3.linear.FieldVector<T>,org.apache.commons.math3.linear.FieldVector<T>)";
    static String m7 = p + "ArrayFieldVector(org.apache.commons.math3.linear.FieldVector<T>,T[])";
    static String m8 = p + "ArrayFieldVector(T[],org.apache.commons.math3.linear.ArrayFieldVector<T>)";
    static String m9 = p + "ArrayFieldVector(T[],org.apache.commons.math3.linear.FieldVector<T>)";
    static String m10 = p + "ArrayFieldVector(T[],T[])";
    
    static String all = m1+";"+m2+";"+m3+";"+m4+";"+m5+";"+m6+";"+m7+";"+m8+";"+m9+";"+m10;
    
    @Test public void gitbug481a1() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a1", "-cp", "test/gitbug481b","-method="+m1,"-no-staticInitWarning");
    }

    @Test public void gitbug481a2() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a2", "-cp", "test/gitbug481b","-method="+m2,"-no-staticInitWarning");
    }

    @Test public void gitbug481a3() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a3", "-cp", "test/gitbug481b","-method="+m3,"-no-staticInitWarning");
    }

    @Test public void gitbug481a4() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a4", "-cp", "test/gitbug481b","-method="+m4,"-no-staticInitWarning");
    }

    @Test public void gitbug481a5() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a5", "-cp", "test/gitbug481b","-method="+m5,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a6() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a6", "-cp", "test/gitbug481b","-method="+m6,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a7() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a7", "-cp", "test/gitbug481b","-method="+m7,"-no-staticInitWarning");
    }

    @Test public void gitbug481a8() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a8", "-cp", "test/gitbug481b","-method="+m8,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a9() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a9", "-cp", "test/gitbug481b","-method="+m9,"-no-staticInitWarning");
    }

    @Ignore // FIXME - Out of memory
    @Test public void gitbug481a10() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a10", "-cp", "test/gitbug481b","-method="+m10,"-no-staticInitWarning","-solver-seed=42");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481arest() {
        expectedExit = 1;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a", "-cp", "test/gitbug481b","-exclude="+all,"-no-staticInitWarning","-solver-seed=142");
    }

    @Test public void gitbug482() {
        expectedExit = 0;
        helpTCF("test/gitbug482/checkers/src/main/java/checkers/*.java","test/gitbug482", "-cp", "test/gitbug482/checkers/src/main","-check"); // check only, not esc
    }

    @Test public void gitbug556() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug557() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug558() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug558a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug558b() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug559() {
        expectedExit = 0;
        helpTCG("-escExitInfo");
    }
    
    @Test public void gitbug559a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug560() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug567() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug567a() {
        expectedExit = 0;
        helpTCF("test/gitbug567","test/gitbug567a","-code-math=java");
    }
    
    @Test public void gitbug567b() {
        expectedExit = 0;
        helpTCF("test/gitbug567","test/gitbug567b","-code-math=safe");
    }
    
    @Test public void gitbug567c() {
        expectedExit = 0;
        helpTCF("test/gitbug567","test/gitbug567c","-code-math=bigint");
    }
    
    @Test public void gitbug572() {
        expectedExit = 1;
        helpTCG();
    }
    
    // The .jml file is on the command-line, which caused a crash, now fixed
    @Test public void gitbug573() {
        expectedExit = 0;
        helpTCF("test/gitbug573/pckg/A.jml","test/gitbug573","-sourcepath","test/gitbug573");
    }
    
    @Test public void gitbug573a() {
        expectedExit = 0;
        helpTCG();
    }
    
    // Here .jml is on the command-line, but the .java does not exist
    @Test public void gitbug573b() {
        expectedExit = 1;
        helpTCF("test/gitbug573b/pckg/A.jml","test/gitbug573b","-sourcepath","test/gitbug573b");
    }
    
    @Test public void gitbug573c() {
        expectedExit = 1;
        helpTCF("test/gitbug573c/java/lang/Integer.jml","test/gitbug573c","-sourcepath","test/gitbug573c","-no-internalSpecs");
    }
    
    @Test public void gitbug574() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug575() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug578() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Ignore // FIXME -  Needs more double specs
    @Test public void gitbug580() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug582() {
        expectedExit = 0;
        helpTCG("-purityCheck");
    }
    
    @Test
    public void gitbug589() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug591() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug593() {
        expectedExit = 0;
        helpTCG("-check");
    }
    
    @Test
    public void gitbug594() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596b() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596c() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596d() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug597() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug598() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug598a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug600() {
        expectedExit = 0;
        helpTCG("-rac","-racCheckAssumptions","-racPreconditionEntry"); // RAC compile crash
    }
    
    @Ignore // FIXME - times out -- double arithmetic?
    @Test
    public void gitbug601() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug602() {
        expectedExit = 0;
        helpTCG("-Xlint:unchecked","-Xlint:sunapi");
    }
    
    @Test
    public void gitbug603() {
        expectedExit = Main.Result.CMDERR.exitCode;
        helpTCG("-Xmaxwarns=100","-quiet"); // Arguments are part of the test
    }
    
    @Ignore   // FIXME requires implementation of \not_assigned
    @Test
    public void gitbug604() {
        expectedExit = 0;
        helpTCG("-code-math=safe","-method=AbsInterval.add");
    }
    
    @Test
    public void gitbug605() {
        expectedExit = 0;
        helpTCG("-code-math=safe");
    }
    
    @Test
    public void gitbug606() {
        expectedExit = 0;
        helpTCG("-code-math=safe");
    }
    
    @Test
    public void gitbug607() {
        expectedExit = 0;
        helpTCG("-show","-method=x"); // Arguments are part of the test
    }
    
    @Test
    public void gitbug608() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug610() {
        expectedExit = 0;
        helpTCG("-code-math=safe");
    }
    
    @Test
    public void gitbug611() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug613() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug615() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug618() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug621() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug621a() { // Original bug
        expectedExit = 0;
        helpTCG("-method=testMethod"); // Limited to this one method
    }
    
    @Test
    public void gitbug622() { // Problem with implicit assertion about string literal
        expectedExit = 0;
        helpTCG("-staticInitWarning");
    }
    
    @Test 
    public void gitbug622a() { // Problem with implicit assertion about string literal
        expectedExit = 0;
        helpTCG("-no-staticInitWarning");
    }
    
    @Test
    public void gitbug623() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Ignore // Varying test output in trace
    @Test
    public void gitbug626() {
        expectedExit = 0;
        helpTCG("-subexpressions");
    }
    
    @Ignore // FIXME - Problem with fresh in loop bodies
    @Test
    public void gitbug627() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug629() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug629a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug630() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug630a() { // FIXME - SMT encpoding problem
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug631() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test @Ignore  // Needs specs about double
    public void gitbug633() {
        Assume.assumeTrue(runLongTests); // FIXME - And not yet working either
        cpathAddition = ":../OpenJML/runtime";
        expectedExit = 0;
        helpTCG();
    }
    
    @Test  // Z3 non-deterministically crashes; trying to fix that by specifying the seed
    public void gitbug633a() {
        expectedExit = 0;
        helpTCG("-solver-seed=42");
    }
    
    @Test
    public void gitbug634() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug635() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug636() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug637() {
        expectedExit = 0;
        helpTCG();
    }

    @Test
    public void gitbug638() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
   public void gitbug639() {
       expectedExit = 0;
       helpTCG();
   }
   
    @Test
   public void gitbug639a() {
       expectedExit = 0;
       helpTCG();
   }
   
    @Test
    public void gitbug640() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug643() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug644() {
        expectedExit = 0;
        helpTCG();
    }
        
    @Test @Ignore // FIXME - needs to be RAC and to be fixed
    public void gitbug645() {
        expectedExit = 0;
        helpTCG("-rac");
    }
    
    @Test
    public void gitbug647() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug648() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test // Errors encountered when using runtime on the classpath
    public void gitbug648a() {
        expectedExit = 1;
        helpTCF("test/gitbug648a","test/gitbug648a","-cp","test/gitbug648:../OpenJML/runtime");
    }
    
    @Test
    public void gitbug650() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug650a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug650b() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug650c() {
        expectedExit = 0;
        helpTCG();
    }

    @Test
    public void gitbug651() {
        expectedExit = 0;
        helpTCG();
    }

    @Test @Ignore // FIXME - needs some implementation
    public void gitbug651a() {
        expectedExit = 0;
        helpTCG();
    }

    @Test
    public void gitbug653() {
        expectedExit = 0;
        helpTCG("-specspath=test/gitbug653");
    }
    
    @Test
    public void gitbug654() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug659() {
        expectedExit = 0;
        helpTCG();
    }
    
    
    @Test
    public void gitbug667() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug669() {
        expectedExit = 0;
    }
    
    @Test
    public void gitbug666() {  // FIXME - recursive -- not yet fixed
        expectedExit = 0;
    }
    
    @Test
    public void gitbug670() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test @Ignore // FIXME -- nullpointer exception, time out //  // Complained of infinite run time
    public void gitbug672() {
        expectedExit = 0;
        helpTCF("test/gitbug672/commons-collections4-4.3-sources/org/apache/commons/collections4/bidimap/TreeBidiMap.java","test/gitbug672","-timeout=1800","-no-staticInitWarning","-cp","test/gitbug672/commons-collections4-4.3-sources","-escMaxWarnings=1");
    }
    
    @Test  @Ignore // FIXME -- MISMATCHED BLOCKS // // Complained of undefined symbols
    public void gitbug671() {
        expectedExit = 0;
        helpTCF("test/gitbug672/commons-collections4-4.3-sources/org/apache/commons/collections4/set/ListOrderedSet.java","test/gitbug671","-timeout=1800","-no-staticInitWarning","-cp","test/gitbug672/commons-collections4-4.3-sources","-escMaxWarnings=1");
    }
    
    @Test
    public void gitbug673() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug676() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test @Ignore // FIXME - this seems to be an incompleteness or bug in Z3 non-linear computations
    public void gitbug677() {
        expectedExit = 0;
        helpTCG("-code-math=safe");//,"-show","-method=calculateArea","-subexpressions","-ce"); // The problem manifests with safe math
    }
    
    @Test
    public void gitbug678() {
        expectedExit = 0;
        helpTCG("-method=DoubleAbsolute");
    }
    
    @Test
    public void gitbug681() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug682() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug683() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug684() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug685() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug686() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug687() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug688() {
        expectedExit = 0;
        helpTCG("-subexpressions");
    }
    
    @Test
    public void gitbug695() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug696() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug698() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test @Ignore // Will erroneously succeed until measured_by is implemented
    public void gitbug705() {
        expectedExit = 0;
        helpTCG();
    }

    @Test @Ignore // FIXME: Bug fixed, but the specs are not complete
    public void gitbug710() {
        expectedExit = 0;
        helpTCF("test/gitbug710/java/util/IdentityHashMap.java", "test/gitbug710","-cp","test/gitbug710","-no-staticInitWarning","-timeout=300");
    }
    
    @Test
    public void gitbug711() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug712() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug716() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test @Ignore // FIXME: EXAMPLE SPECS NOT YET COMPLETE
    public void gitbug717() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test @Ignore // FIXME: Specs not yet finished
    public void gitbug718() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug718a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug718x1() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug718x2() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug718x3() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug718x4() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug719() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug719a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug722() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug732() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug733() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug733a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug734() {
        expectedExit = 0;
        helpTCG();
    }
    
    public void gitbug888() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug999() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void rise4fun() {
        expectedExit = 0;
        helpTCGNoOptions();
    }

}

