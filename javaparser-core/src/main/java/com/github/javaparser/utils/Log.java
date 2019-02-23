package com.github.javaparser.utils;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.function.Supplier;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * To avoid dependencies on logging frameworks, we have invented yet another logging framework :-)
 * <p>
 * See <a href="http://javaparser.org/javaparsers-logging-framework-in-one-file/">a blog about this</a>
 */
public class Log {
    /**
     * This adapter logs to standard out and standard error.
     */
    public static class StandardOutStandardErrorAdapter implements Adapter {
        @Override
        public void info(Supplier<String> messageSupplier) {
            System.out.println(messageSupplier.get());
        }

        @Override
        public void trace(Supplier<String> messageSupplier) {
            System.out.println(messageSupplier.get());
        }

        @Override
        public void error(Supplier<Throwable> throwableSupplier, Supplier<String> messageSupplier) {
            Throwable throwable = throwableSupplier.get();
            String message = messageSupplier.get();
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
                trace(sw::toString);
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
        public void info(Supplier<String> messageSupplier) {
        }

        @Override
        public void trace(Supplier<String> messageSupplier) {
        }

        @Override
        public void error(Supplier<Throwable> throwableSupplier, Supplier<String> messageSupplier) {
        }
    }

    public interface Adapter {

        void info(Supplier<String> message);

        void trace(Supplier<String> message);

        /**
         * Both can supply a null.
         */
        void error(Supplier<Throwable> throwableSupplier, Supplier<String> messageSupplier);
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
    @SafeVarargs
    public static void trace(String format, Supplier<Object>... args) {
        CURRENT_ADAPTER.trace(makeFormattingSupplier(format, args));
    }

    private static Supplier<String> makeFormattingSupplier(String format, Supplier<Object>[] args) {
        return () -> {
            Object[] objects = new Object[args.length];
            for (int i = 0; i < args.length; i++) {
                objects[i] = args[i].get();
            }
            return f(format, objects);
        };
    }


    /**
     * For logging things that are nice to see scrolling by.
     */
    @SafeVarargs
    public static void info(String format, Supplier<Object>... args) {
        CURRENT_ADAPTER.info(makeFormattingSupplier(format, args));
    }

    /**
     * For drawing attention to an error.
     */
    public static void error(Throwable throwable) {
        CURRENT_ADAPTER.error(() -> throwable, null);
    }

    /**
     * For drawing attention to an error that you don't have an exception for.
     */
    @SafeVarargs
    public static void error(Throwable throwable, String format, Supplier<Object>... args) {
        CURRENT_ADAPTER.error(() -> throwable, makeFormattingSupplier(format, args));
    }

    /**
     * For drawing attention to an error that you don't have an exception for.
     */
    @SafeVarargs
    public static void error(String format, Supplier<Object>... args) {
        CURRENT_ADAPTER.error(() -> null, makeFormattingSupplier(format, args));
    }
}
