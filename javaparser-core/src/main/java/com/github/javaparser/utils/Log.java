package com.github.javaparser.utils;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * To avoid dependencies on logging frameworks, we have invented yet another logging framework :-)
 */
public class Log {
    /**
     * This adapter logs to standard out and standard error.
     */
    public static class StandardOutStandardErrorAdapter implements Adapter {
        @Override
        public void info(String message) {
            System.out.println(message);
        }

        @Override
        public void trace(String message) {
            System.out.println(message);
        }

        @Override
        public void error(Throwable throwable, String message) {
            if (message == null) {
                System.err.println(throwable.getMessage());
                printStackTrace(throwable);
            } else if (throwable == null) {
                System.err.println(message);
            } else {
                System.err.println(message + ":" + throwable.getMessage());
                printStackTrace(throwable);
            }
        }

        private void printStackTrace(Throwable throwable) {
            try (StringWriter sw = new StringWriter(); PrintWriter pw = new PrintWriter(sw)) {
                throwable.printStackTrace(pw);
                trace(sw.toString());
            } catch (IOException e) {
                throw new AssertionError("Error in logging library");
            }
        }
    }

    /**
     * This adapter logs nothing.
     */
    public static class SilentAdapter implements Adapter {
        @Override
        public void info(String message) {
        }

        @Override
        public void trace(String message) {
        }

        @Override
        public void error(Throwable throwable, String f) {
        }
    }

    public interface Adapter {

        void info(String message);

        void trace(String message);

        /**
         * Both can be null.
         */
        void error(Throwable throwable, String f);
    }

    private static Adapter CURRENT_ADAPTER = new SilentAdapter();

    /**
     * Change how logging is handled. You can set your own implementation that forwards to your logging library.
     */
    public static void setAdapter(Adapter adapter) {
        CURRENT_ADAPTER = adapter;
    }

    /**
     * For logging information that may help solving a problem.
     */
    public static void trace(String format, Object... args) {
        CURRENT_ADAPTER.trace(f(format, args));
    }

    /**
     * For logging things that are nice to see scrolling by.
     */
    public static void info(String format, Object... args) {
        CURRENT_ADAPTER.info(f(format, args));
    }

    /**
     * For drawing attention to an error.
     */
    public static void error(Throwable throwable) {
        CURRENT_ADAPTER.error(throwable, null);
    }

    /**
     * For drawing attention to an error that you don't have an exception for.
     */
    public static void error(Throwable throwable, String format, Object... args) {
        CURRENT_ADAPTER.error(throwable, f(format, args));
    }

    /**
     * For drawing attention to an error that you don't have an exception for.
     */
    public static void error(String format, Object... args) {
        CURRENT_ADAPTER.error(null, f(format, args));
    }
}
