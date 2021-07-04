package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

/** These tests use the internal specs so that they trigger any checking of
 * specs that are referenced by Object.
 * @author David Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class internalSpecs extends TCBase {


    @Override
    public void setUp() throws Exception {
//      noCollectDiagnostics = true;
//      jmldebug = true;
        useSystemSpecs = true;
        super.setUp();
        main.addOptions("-no-purityCheck"); // FIXME - there are too many purity problems in the specs right now
    }

    /** Scan something very simple but use the internal spaces to see what 
     * problems there might be in the specs and to be sure they are pulled in. */
    @Test
    public void testPure() {
        helpTC(" class A { /*@ pure */ boolean m() { return true; }  \n //@ invariant m(); \n}"
        );
    }

}
