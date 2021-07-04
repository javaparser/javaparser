package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.models.JMLByte;

import org.junit.Test;

// Tests that the models are present
// TODO : lots more tests of models

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class misctests {

    @Test
    public void test1() {
        JMLByte b = new JMLByte((byte)1);
    }
    
    @Test
    public void test2() {
        JMLByte b = new JMLByte((byte)1);
        Object bb = b.clone();
    }
    
}
