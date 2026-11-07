package com.example.service.impl;

import com.example.service.*;

public class RecordServiceImpl
        extends com.example.core.service.impl.RecordServiceImpl {

    private static final CreateProcessor createProcessor = new CreateProcessor() {
        @Override
        public void after(Record record) {
        }
    };
}
