package com.github.javaparser.jml;

import lombok.SneakyThrows;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (1/30/20)
 */
public class JmlFacade {
    public static String getVersion() {
        InputStream in = JmlFacade.class.getResourceAsStream("/jml-extract.version");
        if (in == null) return "n/a";
        try {
            return JmlFacade.readString(in);
        } finally {
            try {
                in.close();
            } catch (IOException ignored) {
            }
        }
    }


    static String readString(String fileName) throws IOException {
        byte[] b = Files.readAllBytes(Paths.get(fileName));
        return new String(b, StandardCharsets.UTF_8);
    }

    static String readString(InputStream in) {
        StringWriter writer = new StringWriter();
        try (final InputStreamReader r = new InputStreamReader(in)) {
            char[] b = new char[4 * 1024];
            int len = -1;
            while ((len = r.read(b)) > 0) {
                writer.write(b, 0, len);
            }
        } catch (IOException ignored) {
        }
        return writer.toString();
    }


    static List<Path> getFiles(String[] paths) {
        return Arrays.stream(paths).flatMap(JmlFacade::getFiles).collect(Collectors.toList());
    }

    @SneakyThrows
    static Stream<Path> getFiles(String path) {
        Path p = Paths.get(path);
        if (Files.isDirectory(p))
            return Files.walk(p).filter(it -> !Files.isDirectory(it));
        else
            return Stream.of(p);
    }
}
