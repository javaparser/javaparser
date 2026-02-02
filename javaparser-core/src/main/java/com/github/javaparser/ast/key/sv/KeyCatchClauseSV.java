package com.github.javaparser.ast.key.sv;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;

/**
 * @author Alexander Weigl
 * @version 1 (10/31/21)
 */
public class KeyCatchClauseSV extends CatchClause {

    private final String schemaVar;

    public KeyCatchClauseSV(TokenRange range, String text) {
        super(range, new Parameter(), new BlockStmt());
        this.schemaVar = text;
    }

    public String getSchemaVar() {
        return schemaVar;
    }
}
