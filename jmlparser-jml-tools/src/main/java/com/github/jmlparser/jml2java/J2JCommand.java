package com.github.jmlparser.jml2java;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
@Parameters(commandNames = {"jml2java"},
        commandDescription = "Submit usage for a given customer and subscription, accepts one usage item")
public class J2JCommand {
    @Parameter(names = {"-o", "--output"}, description = "Output folder of the Java Files")
    private File outputFolder = new File("out");

    @Parameter(names = {"--jbmc"}, description = "JBMC mode")
    private boolean jjbmcMode = false;
    @Parameter(description = "FILES")
    private List<String> files = new ArrayList<>();
}
