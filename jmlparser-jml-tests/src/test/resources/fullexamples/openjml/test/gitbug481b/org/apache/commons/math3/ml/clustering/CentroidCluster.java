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
package org.apache.commons.math3.ml.clustering;

/**
 * A Cluster used by centroid-based clustering algorithms.
 * <p>
 * Defines additionally a cluster center which may not necessarily be a member
 * of the original data set.
 *
 * @param <T> the type of points that can be clustered
 * @since 3.2
 */
public class CentroidCluster<T extends Clusterable> extends Cluster<T> {

    /** Serializable version identifier. */
    private static final long serialVersionUID = -3075288519071812288L;

    /** Center of the cluster. */
    private final Clusterable center;

    /**
     * Build a cluster centered at a specified point.
     * @param center the point which is to be the center of this cluster
     */
    public CentroidCluster(final Clusterable center) {
        super();
        this.center = center;
    }

    /**
     * Get the point chosen to be the center of this cluster.
     * @return chosen cluster center
     */
    public Clusterable getCenter() {
        return center;
    }

}
