
* [ ] Implement ghost labels 
  ```
  //@ lbl: {}
  
  //@ lbl: 
  a := x;
  ```
  
  Ghost labels should be converted into JmlGhostLabelStmt, which
  should behave (except for printing) like a LabeledStmts. 
  
  Maybe we could reuse the original Java AST class and add a flag.
  
* [ ] OPEN:   `begin` and `end` markers for marking of blocks.
  This requires a special treatment and post-processor. 
