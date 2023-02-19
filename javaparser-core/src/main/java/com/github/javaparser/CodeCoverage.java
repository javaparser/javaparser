package com.github.javaparser;
import java.io.*;
import java.util.Arrays;

/**
 * Used to check the branch coverage of a function.
 */
public class CodeCoverage {
    private static boolean[] codeCoverageArr = new boolean[100];

    /**
     * Used to keep track of the branches that have been taken in a given function.
     * @param id for a given branch.
     */
    public static void setFlag(int id) {
        codeCoverageArr[id] = true;
    }


    /**
     * Concatenate the ID's of the set flags to one string, which is then return.
     * @return String containing all the set flags from array codeCoverageArr.
     */
    public static String getTestInfo() {
        String branches = "";
        for(int i=0; i < 100; i++) {
            boolean flag = codeCoverageArr[i];
            if(flag) {
                branches += i + " ";
            }
        }
        return branches;
    }

    /**
     * Resets the array codeCoverageArr
     */
    public static void clearFlagArr() {
        Arrays.fill(codeCoverageArr,false);
    }


    /**
     * Creates file and then writes the branch coverage information the file.
     */
    public static void writeBranchCoverage(String fileName, String[] testInfo) throws IOException {
        BufferedWriter writer = new BufferedWriter(new FileWriter(fileName));
        for(String elem: testInfo) {
            if (elem != null) {
                writer.write("The branches with " + elem + " has been reached \n");
            }
        }
        writer.close();

    }



}