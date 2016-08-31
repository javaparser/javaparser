package com.github.javaparser;

import java.util.List;

public class ParseProblemException extends Exception {
  public final List<Problem> problems;

  public ParseProblemException(List<Problem> problems) {
    this.problems = problems;
  }
}