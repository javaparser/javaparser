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

package org.apache.commons.math3.ml.neuralnet.twod;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.io.Serializable;
import java.io.ObjectInputStream;
import org.apache.commons.math3.ml.neuralnet.Neuron;
import org.apache.commons.math3.ml.neuralnet.Network;
import org.apache.commons.math3.ml.neuralnet.FeatureInitializer;
import org.apache.commons.math3.ml.neuralnet.SquareNeighbourhood;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.MathInternalError;

/**
 * Neural network with the topology of a two-dimensional surface.
 * Each neuron defines one surface element.
 * <br/>
 * This network is primarily intended to represent a
 * <a href="http://en.wikipedia.org/wiki/Kohonen">
 *  Self Organizing Feature Map</a>.
 *
 * @see org.apache.commons.math3.ml.neuralnet.sofm
 * @since 3.3
 */
public class NeuronSquareMesh2D
    implements Iterable<Neuron>,
               Serializable {
    /** Serial version ID */
    private static final long serialVersionUID = 1L;
    /** Underlying network. */
    private final Network network;
    /** Number of rows. */
    private final int numberOfRows;
    /** Number of columns. */
    private final int numberOfColumns;
    /** Wrap. */
    private final boolean wrapRows;
    /** Wrap. */
    private final boolean wrapColumns;
    /** Neighbourhood type. */
    private final SquareNeighbourhood neighbourhood;
    /**
     * Mapping of the 2D coordinates (in the rectangular mesh) to
     * the neuron identifiers (attributed by the {@link #network}
     * instance).
     */
    private final long[][] identifiers;

    /**
     * Horizontal (along row) direction.
     * @since 3.6
     */
    public enum HorizontalDirection {
        /** Column at the right of the current column. */
       RIGHT,
       /** Current column. */
       CENTER,
       /** Column at the left of the current column. */
       LEFT,
    }
    /**
     * Vertical (along column) direction.
     * @since 3.6
     */
    public enum VerticalDirection {
        /** Row above the current row. */
        UP,
        /** Current row. */
        CENTER,
        /** Row below the current row. */
        DOWN,
    }

    /**
     * Constructor with restricted access, solely used for deserialization.
     *
     * @param wrapRowDim Whether to wrap the first dimension (i.e the first
     * and last neurons will be linked together).
     * @param wrapColDim Whether to wrap the second dimension (i.e the first
     * and last neurons will be linked together).
     * @param neighbourhoodType Neighbourhood type.
     * @param featuresList Arrays that will initialize the features sets of
     * the network's neurons.
     * @throws NumberIsTooSmallException if {@code numRows < 2} or
     * {@code numCols < 2}.
     */
    NeuronSquareMesh2D(boolean wrapRowDim,
                       boolean wrapColDim,
                       SquareNeighbourhood neighbourhoodType,
                       double[][][] featuresList) {
        numberOfRows = featuresList.length;
        numberOfColumns = featuresList[0].length;

        if (numberOfRows < 2) {
            throw new NumberIsTooSmallException(numberOfRows, 2, true);
        }
        if (numberOfColumns < 2) {
            throw new NumberIsTooSmallException(numberOfColumns, 2, true);
        }

        wrapRows = wrapRowDim;
        wrapColumns = wrapColDim;
        neighbourhood = neighbourhoodType;

        final int fLen = featuresList[0][0].length;
        network = new Network(0, fLen);
        identifiers = new long[numberOfRows][numberOfColumns];

        // Add neurons.
        for (int i = 0; i < numberOfRows; i++) {
            for (int j = 0; j < numberOfColumns; j++) {
                identifiers[i][j] = network.createNeuron(featuresList[i][j]);
            }
        }

        // Add links.
        createLinks();
    }

    /**
     * Creates a two-dimensional network composed of square cells:
     * Each neuron not located on the border of the mesh has four
     * neurons linked to it.
     * <br/>
     * The links are bi-directional.
     * <br/>
     * The topology of the network can also be a cylinder (if one
     * of the dimensions is wrapped) or a torus (if both dimensions
     * are wrapped).
     *
     * @param numRows Number of neurons in the first dimension.
     * @param wrapRowDim Whether to wrap the first dimension (i.e the first
     * and last neurons will be linked together).
     * @param numCols Number of neurons in the second dimension.
     * @param wrapColDim Whether to wrap the second dimension (i.e the first
     * and last neurons will be linked together).
     * @param neighbourhoodType Neighbourhood type.
     * @param featureInit Array of functions that will initialize the
     * corresponding element of the features set of each newly created
     * neuron. In particular, the size of this array defines the size of
     * feature set.
     * @throws NumberIsTooSmallException if {@code numRows < 2} or
     * {@code numCols < 2}.
     */
    public NeuronSquareMesh2D(int numRows,
                              boolean wrapRowDim,
                              int numCols,
                              boolean wrapColDim,
                              SquareNeighbourhood neighbourhoodType,
                              FeatureInitializer[] featureInit) {
        if (numRows < 2) {
            throw new NumberIsTooSmallException(numRows, 2, true);
        }
        if (numCols < 2) {
            throw new NumberIsTooSmallException(numCols, 2, true);
        }

        numberOfRows = numRows;
        wrapRows = wrapRowDim;
        numberOfColumns = numCols;
        wrapColumns = wrapColDim;
        neighbourhood = neighbourhoodType;
        identifiers = new long[numberOfRows][numberOfColumns];

        final int fLen = featureInit.length;
        network = new Network(0, fLen);

        // Add neurons.
        for (int i = 0; i < numRows; i++) {
            for (int j = 0; j < numCols; j++) {
                final double[] features = new double[fLen];
                for (int fIndex = 0; fIndex < fLen; fIndex++) {
                    features[fIndex] = featureInit[fIndex].value();
                }
                identifiers[i][j] = network.createNeuron(features);
            }
        }

        // Add links.
        createLinks();
    }

    /**
     * Constructor with restricted access, solely used for making a
     * {@link #copy() deep copy}.
     *
     * @param wrapRowDim Whether to wrap the first dimension (i.e the first
     * and last neurons will be linked together).
     * @param wrapColDim Whether to wrap the second dimension (i.e the first
     * and last neurons will be linked together).
     * @param neighbourhoodType Neighbourhood type.
     * @param net Underlying network.
     * @param idGrid Neuron identifiers.
     */
    private NeuronSquareMesh2D(boolean wrapRowDim,
                               boolean wrapColDim,
                               SquareNeighbourhood neighbourhoodType,
                               Network net,
                               long[][] idGrid) {
        numberOfRows = idGrid.length;
        numberOfColumns = idGrid[0].length;
        wrapRows = wrapRowDim;
        wrapColumns = wrapColDim;
        neighbourhood = neighbourhoodType;
        network = net;
        identifiers = idGrid;
    }

    /**
     * Performs a deep copy of this instance.
     * Upon return, the copied and original instances will be independent:
     * Updating one will not affect the other.
     *
     * @return a new instance with the same state as this instance.
     * @since 3.6
     */
    public synchronized NeuronSquareMesh2D copy() {
        final long[][] idGrid = new long[numberOfRows][numberOfColumns];
        for (int r = 0; r < numberOfRows; r++) {
            for (int c = 0; c < numberOfColumns; c++) {
                idGrid[r][c] = identifiers[r][c];
            }
        }

        return new NeuronSquareMesh2D(wrapRows,
                                      wrapColumns,
                                      neighbourhood,
                                      network.copy(),
                                      idGrid);
    }

    /**
     * {@inheritDoc}
     *  @since 3.6
     */
    public Iterator<Neuron> iterator() {
        return network.iterator();
    }

    /**
     * Retrieves the underlying network.
     * A reference is returned (enabling, for example, the network to be
     * trained).
     * This also implies that calling methods that modify the {@link Network}
     * topology may cause this class to become inconsistent.
     *
     * @return the network.
     */
    public Network getNetwork() {
        return network;
    }

    /**
     * Gets the number of neurons in each row of this map.
     *
     * @return the number of rows.
     */
    public int getNumberOfRows() {
        return numberOfRows;
    }

    /**
     * Gets the number of neurons in each column of this map.
     *
     * @return the number of column.
     */
    public int getNumberOfColumns() {
        return numberOfColumns;
    }

    /**
     * Retrieves the neuron at location {@code (i, j)} in the map.
     * The neuron at position {@code (0, 0)} is located at the upper-left
     * corner of the map.
     *
     * @param i Row index.
     * @param j Column index.
     * @return the neuron at {@code (i, j)}.
     * @throws OutOfRangeException if {@code i} or {@code j} is
     * out of range.
     *
     * @see #getNeuron(int,int,HorizontalDirection,VerticalDirection)
     */
    public Neuron getNeuron(int i,
                            int j) {
        if (i < 0 ||
            i >= numberOfRows) {
            throw new OutOfRangeException(i, 0, numberOfRows - 1);
        }
        if (j < 0 ||
            j >= numberOfColumns) {
            throw new OutOfRangeException(j, 0, numberOfColumns - 1);
        }

        return network.getNeuron(identifiers[i][j]);
    }

    /**
     * Retrieves the neuron at {@code (location[0], location[1])} in the map.
     * The neuron at position {@code (0, 0)} is located at the upper-left
     * corner of the map.
     *
     * @param row Row index.
     * @param col Column index.
     * @param alongRowDir Direction along the given {@code row} (i.e. an
     * offset will be added to the given <em>column</em> index.
     * @param alongColDir Direction along the given {@code col} (i.e. an
     * offset will be added to the given <em>row</em> index.
     * @return the neuron at the requested location, or {@code null} if
     * the location is not on the map.
     *
     * @see #getNeuron(int,int)
     */
    public Neuron getNeuron(int row,
                            int col,
                            HorizontalDirection alongRowDir,
                            VerticalDirection alongColDir) {
        final int[] location = getLocation(row, col, alongRowDir, alongColDir);

        return location == null ? null : getNeuron(location[0], location[1]);
    }

    /**
     * Computes the location of a neighbouring neuron.
     * It will return {@code null} if the resulting location is not part
     * of the map.
     * Position {@code (0, 0)} is at the upper-left corner of the map.
     *
     * @param row Row index.
     * @param col Column index.
     * @param alongRowDir Direction along the given {@code row} (i.e. an
     * offset will be added to the given <em>column</em> index.
     * @param alongColDir Direction along the given {@code col} (i.e. an
     * offset will be added to the given <em>row</em> index.
     * @return an array of length 2 containing the indices of the requested
     * location, or {@code null} if that location is not part of the map.
     *
     * @see #getNeuron(int,int)
     */
    private int[] getLocation(int row,
                              int col,
                              HorizontalDirection alongRowDir,
                              VerticalDirection alongColDir) {
        final int colOffset;
        switch (alongRowDir) {
        case LEFT:
            colOffset = -1;
            break;
        case RIGHT:
            colOffset = 1;
            break;
        case CENTER:
            colOffset = 0;
            break;
        default:
            // Should never happen.
            throw new MathInternalError();
        }
        int colIndex = col + colOffset;
        if (wrapColumns) {
            if (colIndex < 0) {
                colIndex += numberOfColumns;
            } else {
                colIndex %= numberOfColumns;
            }
        }

        final int rowOffset;
        switch (alongColDir) {
        case UP:
            rowOffset = -1;
            break;
        case DOWN:
            rowOffset = 1;
            break;
        case CENTER:
            rowOffset = 0;
            break;
        default:
            // Should never happen.
            throw new MathInternalError();
        }
        int rowIndex = row + rowOffset;
        if (wrapRows) {
            if (rowIndex < 0) {
                rowIndex += numberOfRows;
            } else {
                rowIndex %= numberOfRows;
            }
        }

        if (rowIndex < 0 ||
            rowIndex >= numberOfRows ||
            colIndex < 0 ||
            colIndex >= numberOfColumns) {
            return null;
        } else {
            return new int[] { rowIndex, colIndex };
        }
    }

    /**
     * Creates the neighbour relationships between neurons.
     */
    private void createLinks() {
        // "linkEnd" will store the identifiers of the "neighbours".
        final List<Long> linkEnd = new ArrayList<Long>();
        final int iLast = numberOfRows - 1;
        final int jLast = numberOfColumns - 1;
        for (int i = 0; i < numberOfRows; i++) {
            for (int j = 0; j < numberOfColumns; j++) {
                linkEnd.clear();

                switch (neighbourhood) {

                case MOORE:
                    // Add links to "diagonal" neighbours.
                    if (i > 0) {
                        if (j > 0) {
                            linkEnd.add(identifiers[i - 1][j - 1]);
                        }
                        if (j < jLast) {
                            linkEnd.add(identifiers[i - 1][j + 1]);
                        }
                    }
                    if (i < iLast) {
                        if (j > 0) {
                            linkEnd.add(identifiers[i + 1][j - 1]);
                        }
                        if (j < jLast) {
                            linkEnd.add(identifiers[i + 1][j + 1]);
                        }
                    }
                    if (wrapRows) {
                        if (i == 0) {
                            if (j > 0) {
                                linkEnd.add(identifiers[iLast][j - 1]);
                            }
                            if (j < jLast) {
                                linkEnd.add(identifiers[iLast][j + 1]);
                            }
                        } else if (i == iLast) {
                            if (j > 0) {
                                linkEnd.add(identifiers[0][j - 1]);
                            }
                            if (j < jLast) {
                                linkEnd.add(identifiers[0][j + 1]);
                            }
                        }
                    }
                    if (wrapColumns) {
                        if (j == 0) {
                            if (i > 0) {
                                linkEnd.add(identifiers[i - 1][jLast]);
                            }
                            if (i < iLast) {
                                linkEnd.add(identifiers[i + 1][jLast]);
                            }
                        } else if (j == jLast) {
                             if (i > 0) {
                                 linkEnd.add(identifiers[i - 1][0]);
                             }
                             if (i < iLast) {
                                 linkEnd.add(identifiers[i + 1][0]);
                             }
                        }
                    }
                    if (wrapRows &&
                        wrapColumns) {
                        if (i == 0 &&
                            j == 0) {
                            linkEnd.add(identifiers[iLast][jLast]);
                        } else if (i == 0 &&
                                   j == jLast) {
                            linkEnd.add(identifiers[iLast][0]);
                        } else if (i == iLast &&
                                   j == 0) {
                            linkEnd.add(identifiers[0][jLast]);
                        } else if (i == iLast &&
                                   j == jLast) {
                            linkEnd.add(identifiers[0][0]);
                        }
                    }

                    // Case falls through since the "Moore" neighbourhood
                    // also contains the neurons that belong to the "Von
                    // Neumann" neighbourhood.

                    // fallthru (CheckStyle)
                case VON_NEUMANN:
                    // Links to preceding and following "row".
                    if (i > 0) {
                        linkEnd.add(identifiers[i - 1][j]);
                    }
                    if (i < iLast) {
                        linkEnd.add(identifiers[i + 1][j]);
                    }
                    if (wrapRows) {
                        if (i == 0) {
                            linkEnd.add(identifiers[iLast][j]);
                        } else if (i == iLast) {
                            linkEnd.add(identifiers[0][j]);
                        }
                    }

                    // Links to preceding and following "column".
                    if (j > 0) {
                        linkEnd.add(identifiers[i][j - 1]);
                    }
                    if (j < jLast) {
                        linkEnd.add(identifiers[i][j + 1]);
                    }
                    if (wrapColumns) {
                        if (j == 0) {
                            linkEnd.add(identifiers[i][jLast]);
                        } else if (j == jLast) {
                            linkEnd.add(identifiers[i][0]);
                        }
                    }
                    break;

                default:
                    throw new MathInternalError(); // Cannot happen.
                }

                final Neuron aNeuron = network.getNeuron(identifiers[i][j]);
                for (long b : linkEnd) {
                    final Neuron bNeuron = network.getNeuron(b);
                    // Link to all neighbours.
                    // The reverse links will be added as the loop proceeds.
                    network.addLink(aNeuron, bNeuron);
                }
            }
        }
    }

    /**
     * Prevents proxy bypass.
     *
     * @param in Input stream.
     */
    private void readObject(ObjectInputStream in) {
        throw new IllegalStateException();
    }

    /**
     * Custom serialization.
     *
     * @return the proxy instance that will be actually serialized.
     */
    private Object writeReplace() {
        final double[][][] featuresList = new double[numberOfRows][numberOfColumns][];
        for (int i = 0; i < numberOfRows; i++) {
            for (int j = 0; j < numberOfColumns; j++) {
                featuresList[i][j] = getNeuron(i, j).getFeatures();
            }
        }

        return new SerializationProxy(wrapRows,
                                      wrapColumns,
                                      neighbourhood,
                                      featuresList);
    }

    /**
     * Serialization.
     */
    private static class SerializationProxy implements Serializable {
        /** Serializable. */
        private static final long serialVersionUID = 20130226L;
        /** Wrap. */
        private final boolean wrapRows;
        /** Wrap. */
        private final boolean wrapColumns;
        /** Neighbourhood type. */
        private final SquareNeighbourhood neighbourhood;
        /** Neurons' features. */
        private final double[][][] featuresList;

        /**
         * @param wrapRows Whether the row dimension is wrapped.
         * @param wrapColumns Whether the column dimension is wrapped.
         * @param neighbourhood Neighbourhood type.
         * @param featuresList List of neurons features.
         * {@code neuronList}.
         */
        SerializationProxy(boolean wrapRows,
                           boolean wrapColumns,
                           SquareNeighbourhood neighbourhood,
                           double[][][] featuresList) {
            this.wrapRows = wrapRows;
            this.wrapColumns = wrapColumns;
            this.neighbourhood = neighbourhood;
            this.featuresList = featuresList;
        }

        /**
         * Custom serialization.
         *
         * @return the {@link Neuron} for which this instance is the proxy.
         */
        private Object readResolve() {
            return new NeuronSquareMesh2D(wrapRows,
                                          wrapColumns,
                                          neighbourhood,
                                          featuresList);
        }
    }
}
