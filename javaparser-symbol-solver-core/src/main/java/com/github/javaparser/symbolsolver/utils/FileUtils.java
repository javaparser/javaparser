package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.utils.Utils;

import java.io.File;

public class FileUtils {
    
    /*
     * returns true if the filename exists otherwise return false
     */
    public static boolean isValidPath(String filename) {
        File file = new File(filename);
        return file.exists();
    }
    
    /*
     * returns the parent path from the filename as string
     */
    public static String getParentPath(String filename) {
        Utils.assertNotNull(filename);
        int lastIndex = filename.lastIndexOf(File.separator);
        return filename.substring(0, lastIndex);
    }

}
