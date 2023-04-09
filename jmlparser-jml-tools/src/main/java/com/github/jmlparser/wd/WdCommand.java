package com.github.jmlparser.wd;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
@Parameters(commandNames = {"wd"},
        commandDescription = "Well-definedness check for JML files.")
public class WdCommand {
    @Parameter(description = "Files to check")
    private List<String> files = new ArrayList<>();

    public void run() {
        System.out.println(files);
    }
}
