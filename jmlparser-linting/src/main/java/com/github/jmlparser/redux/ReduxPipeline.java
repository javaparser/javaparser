package com.github.jmlparser.redux;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class ReduxPipeline {
    public static class ReduxConfig {
        private final boolean simplifyObjectConstruction = true;
        private final boolean reduceLambdaToInnerClasses = true;
    }
}
