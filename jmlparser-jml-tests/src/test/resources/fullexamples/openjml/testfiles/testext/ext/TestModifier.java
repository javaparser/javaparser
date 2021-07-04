/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package ext;

import org.jmlspecs.openjml.ext.*;


public class TestModifier extends ModifierExtension {

    public String jmlKeyword() {
        return "test";
    }
    
    @Override
    public Class<org.jmlspecs.annotation.Test> javaAnnotation() {
        return org.jmlspecs.annotation.Test.class;
    }
    
    static protected ProgramLocation[] locations = 
        { 
            ProgramLocation.TOP_LEVEL_CLASS,
            ProgramLocation.NESTED_CLASS,
            ProgramLocation.LOCAL_CLASS,
            ProgramLocation.METHOD,
            ProgramLocation.CONSTRUCTOR,
        };
    
    public boolean isAllowed(ProgramLocation loc, boolean isInJML) {
        return isInArray(loc,locations);
    }

}
