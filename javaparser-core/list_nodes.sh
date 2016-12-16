#!/bin/sh
ls -1 src/main/java/com/github/javaparser/ast/*|sed "s|src/main/java/com/github/javaparser/ast/||"|sed "s/\(.*\)\.java/add(\1.class),/" > nodes.txt


