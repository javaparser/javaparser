package com.github.javaparser.bootstrap.metamodel;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

public class OldJavaParserMetaModel {
//
//    public OldJavaParserMetaModel() {
//        for (Class<?> nodeClass : ALL_MODEL_CLASSES) {
//            oldClassMetaModels.add(new OldClassMetaModel(this, nodeClass));
//        }
//        oldClassMetaModels.forEach(OldClassMetaModel::initialize);
//    }
//
//    public List<OldClassMetaModel> getOldClassMetaModels() {
//        return oldClassMetaModels;
//    }
//
//    public Optional<OldClassMetaModel> getClassMetaModel(Class<?> c) {
//        for (OldClassMetaModel oldClassMetaModel : oldClassMetaModels) {
//            if (oldClassMetaModel.getReflectionClass().equals(c)) {
//                return Optional.of(oldClassMetaModel);
//            }
//        }
//        return Optional.empty();
//    }
//
//    @Override
//    public String toString() {
//        StringBuilder b = new StringBuilder();
//        for (OldClassMetaModel oldClassMetaModel : getOldClassMetaModels()) {
//            b.append(oldClassMetaModel).append("\n");
//            for (OldFieldMetaModel oldFieldMetaModel : oldClassMetaModel.getOldFieldMetaModels()) {
//                b.append("\t").append(oldFieldMetaModel).append("\n");
//            }
//        }
//        return b.toString();
//    }
}
