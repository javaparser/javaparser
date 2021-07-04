/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.commons.math3.ml.neuralnet.sofm;

import java.util.Iterator;
import org.apache.commons.math3.ml.neuralnet.Network;

/**
 * Trainer for Kohonen's Self-Organizing Map.
 *
 * @since 3.3
 */
public class KohonenTrainingTask implements Runnable {
    /** SOFM to be trained. */
    private final Network net;
    /** Training data. */
    private final Iterator<double[]> featuresIterator;
    /** Update procedure. */
    private final KohonenUpdateAction updateAction;

    /**
     * Creates a (sequential) trainer for the given network.
     *
     * @param net Network to be trained with the SOFM algorithm.
     * @param featuresIterator Training data iterator.
     * @param updateAction SOFM update procedure.
     */
    public KohonenTrainingTask(Network net,
                               Iterator<double[]> featuresIterator,
                               KohonenUpdateAction updateAction) {
        this.net = net;
        this.featuresIterator = featuresIterator;
        this.updateAction = updateAction;
    }

    /**
     * {@inheritDoc}
     */
    public void run() {
        while (featuresIterator.hasNext()) {
            updateAction.update(net, featuresIterator.next());
        }
    }
}
