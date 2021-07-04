/**
 *  This file is part of miniCDx benchmark of oSCJ.
 *
 *   miniCDx is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   miniCDx is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with miniCDx.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *   Copyright 2009, 2010 
 *   @authors  Daniel Tang, Ales Plsek
 *
 *   See: http://sss.cs.purdue.edu/projects/oscj/
 */
package minicdj.cdx;

/**
 * Noise generator for the detector. The generator lives in the persistent detector scope. Its constructor runs in the
 * persistent detector scope. Noise is generated in the detector scope (and the allocated objects live in the detector
 * scope).
 */
/*@javax.safetycritical.annotate.Scope("cdx.Level0Safelet")*/
/*@javax.safetycritical.annotate.RunsIn("cdx.CollisionDetectorHandler")*/
public class NoiseGenerator {

    private Object[] noiseRoot;
    private int      noisePtr;

    public NoiseGenerator() {
        if (Constants.DETECTOR_NOISE) {
            noiseRoot = new Object[Constants.DETECTOR_NOISE_REACHABLE_POINTERS];
            noisePtr = 0;
        }
    }

    private void generateNoise() {

        for (int i = 0; i < Constants.DETECTOR_NOISE_ALLOCATE_POINTERS; i++) {
            noiseRoot[(noisePtr++) % noiseRoot.length] = new byte[Constants.DETECTOR_NOISE_ALLOCATION_SIZE];
        }

    }

    private void generateNoiseWithVariableObjectSize() {

        int currentIncrement = 0;
        int maxIncrement = Constants.DETECTOR_NOISE_MAX_ALLOCATION_SIZE - Constants.DETECTOR_NOISE_MIN_ALLOCATION_SIZE;

        for (int i = 0; i < Constants.DETECTOR_NOISE_ALLOCATE_POINTERS; i++) {
            noiseRoot[(noisePtr++) % noiseRoot.length] = new byte[Constants.DETECTOR_NOISE_MIN_ALLOCATION_SIZE
                    + (currentIncrement % maxIncrement)];
            currentIncrement += Constants.DETECTOR_NOISE_ALLOCATION_SIZE_INCREMENT;
        }
    }

    public void generateNoiseIfEnabled() {
        if (Constants.DETECTOR_NOISE) {

            if (Constants.DETECTOR_NOISE_VARIABLE_ALLOCATION_SIZE) {
                generateNoiseWithVariableObjectSize();
            } else {
                generateNoise();
            }
        }
    }
}
