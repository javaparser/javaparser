package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.Jmlish;

/**
 * @author Alexander Weigl
 * @version 1 (3/14/21)
 */
public enum Behavior implements Jmlish {
    NONE, BEHAVIOR, NORMAL, EXCEPTIONAL,
    BREAK, CONTINUE, RETURN
}
