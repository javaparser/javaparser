package com.github.jmlparser.pp;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
@Parameters(commandNames = {"format"},
        commandDescription = "Format the JML comments inside Java files.")
public class PrettyPrintCommand {
    @Parameter(description = "Files to check", required = true)
    private List<String> files = new ArrayList<>();

    public void run() {
    }
}
