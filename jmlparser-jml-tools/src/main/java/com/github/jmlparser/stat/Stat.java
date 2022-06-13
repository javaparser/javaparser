package com.github.jmlparser.stat;

import lombok.Data;

import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

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
        private Map<String, CEStat> classExpressionSpecification = new TreeMap<String, CEStat>();
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

        public Map<String, CEStat> getClassExpressionSpecification() {
            return classExpressionSpecification;
        }

        public CEStat getClassExpressionSpecification(String identifier) {
            return classExpressionSpecification.computeIfAbsent(identifier, (k) -> new CEStat());
        }

        @Data
        public class CEStat {
            int numOf;
            int sumOfComplexity;
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
