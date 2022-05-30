package com.github.jmlparser.stat;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.22)
 */
public class Statistics {
    private WcStat java, jml, javaComments, jmlComments;

    public static class WcStat {
        int line;
        int chars;
    }
}
