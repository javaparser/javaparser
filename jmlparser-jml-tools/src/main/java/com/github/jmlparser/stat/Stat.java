package com.github.jmlparser.stat;

import lombok.Data;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (27.05.22)
 */
@Data
public class Stat {
    private int jmlNewlines;
    private int jmlNewlinesNonSanitized;
    private Map<String, ClassStat> classStats = new HashMap<>();

    public void addJmlNewlines(int newlines) {
        jmlNewlines += newlines;
    }

    public ClassStat getClassStats(String fqdn) {
        return classStats.computeIfAbsent(fqdn, k -> new ClassStat());
    }

    @Data
    public static class ClassStat {
        private int numOfInvariants;
        private int lengthOfInvariants;
        private int numOfRepresents;
        private int numOfModelFields;
        private int numOfGhostFields;

        private Map<String, MethodStat> methodStats = new HashMap<>();

        public MethodStat getMethodStats(String signature) {
            return methodStats.computeIfAbsent(signature, k -> new MethodStat());
        }

        public void addNumOfGhostFields(int i) {
            numOfGhostFields += i;
        }

        public void addNumOfModelFields(int i) {
            numOfModelFields += i;
        }
    }

    @Data
    public static class MethodStat {
        private int numOfContracts;

        public void addNumOfContracts(int cnt) {
            numOfContracts += cnt;
        }
    }
}
