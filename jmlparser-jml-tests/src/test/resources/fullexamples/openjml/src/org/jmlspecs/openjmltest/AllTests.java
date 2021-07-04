package org.jmlspecs.openjmltest;

import org.junit.jupiter.api.*;
import org.junit.runner.RunWith;
import org.junit.runners.Suite.SuiteClasses;
import org.openjml.runners.*;

import junit.framework.TestSuite;

import java.io.File;
import java.util.Arrays;

import org.jmlspecs.openjmltest.testcases.*;

//@RunWith(JUnitPlatform.class)
//@SelectPackages({"org.jmlspecs.openjmltest.testcases"})

// This works but is not adaptable if tests are added in the testcases folder
//@RunWith(Suite.class)
//@SuiteClasses({ access.class, api.class, arith.class, assignable.class, binaries.class, bugs.class, compilationUnit.class, compiler.class, deprecation.class, esc.class, escaccessible.class,
//                        escall2.class, escall3.class, escArithmeticModes.class, escArithmeticModes2.class, escbitvector.class, esccallable.class, esccode.class, escConstantFields.class,
//                        escconstructor.class, escCounterexamples.class, escDemofiles.class, escenums.class, escfeatures.class, escfiles.class, escfilesTrace.class, escfunction.class, escgeneric.class,
//                        escinclause.class, escinline.class, escJML.class, esclambdas.class, esclocation.class, escm.class, escnew.class, escnew2.class, escnew3.class, escnewassignable.class,
//                        escnewBoxing.class, escnonpublic.class, escnowarn.class, escoption.class, escprimitivetypes.class, escreadable.class, escstrings.class, escTiming.class, escTrace.class,
//                        escvisibility.class, escvisibility1.class, expressions.class, flow.class, generics.class, harnesstests.class, internalSpecs.class, jmldoc.class, jmltypes.class,
//                        lblexpression.class, matchClasses.class, methodspecs.class, misctests.class, modelghost.class, modifiers.class, namelookup.class, notspecified.class, nowarn.class,
//                        positions.class, prettyprinting.class, purity.class, QueryPure.class, QuerySecret.class, racArithmeticModes.class, racdemoexamples.class, racfeatures.class, racfiles.class,
//                        racJML.class, racnew.class, racnew2.class, racnew3.class, racnewLoops.class, racnewWithSpecs.class, racnonpublic.class, racreadable.class, racsystem.class, redundant.class,
//                        scanner.class, SFBugs.class, SpecsBase.class, SpecsEsc.class, SpecsRac.class, statements.class, strict.class, strongarm.class, sysclasses.class, typechecking.class,
//                        typecheckingJmlTypes.class, typecheckingvisibility.class, typeclauses.class })

// The following runner works with the suite method to add all test case files
// dynamically and explicitly sorts them
@RunWith(org.junit.runners.AllTests.class)
//@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@TestMethodOrder(org.junit.jupiter.api.MethodOrderer.Alphanumeric.class)
@org.junit.jupiter.api.parallel.Execution(org.junit.jupiter.api.parallel.ExecutionMode.CONCURRENT)
public class AllTests {
    
    public static TestSuite suite() {
        try {
            File dir = new File("src/org/jmlspecs/openjmltest/testcases");
            File[] dirs = dir.listFiles();
            Arrays.sort(dirs);
            TestSuite suite = new TestSuite();
            for (File f: dirs) {
                String nm = f.getName();
                if (!nm.endsWith(".java")) continue;
                nm = "org.jmlspecs.openjmltest.testcases." + nm.substring(0, nm.length()-5);
                try {
                    suite.addTest(new junit.framework.JUnit4TestAdapter(Class.forName(nm)));
                } catch (ClassNotFoundException e) {}
            }
            return suite;
        } catch (Exception e) {}
        return null;
    }

}
