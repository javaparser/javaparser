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

package org.apache.commons.math3.geometry.euclidean.threed;

import java.io.Serializable;

import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;

/**
 * This class implements rotations in a three-dimensional space.
 *
 * <p>Rotations can be represented by several different mathematical
 * entities (matrices, axe and angle, Cardan or Euler angles,
 * quaternions). This class presents an higher level abstraction, more
 * user-oriented and hiding this implementation details. Well, for the
 * curious, we use quaternions for the internal representation. The
 * user can build a rotation from any of these representations, and
 * any of these representations can be retrieved from a
 * <code>Rotation</code> instance (see the various constructors and
 * getters). In addition, a rotation can also be built implicitly
 * from a set of vectors and their image.</p>
 * <p>This implies that this class can be used to convert from one
 * representation to another one. For example, converting a rotation
 * matrix into a set of Cardan angles from can be done using the
 * following single line of code:</p>
 * <pre>
 * double[] angles = new Rotation(matrix, 1.0e-10).getAngles(RotationOrder.XYZ);
 * </pre>
 * <p>Focus is oriented on what a rotation <em>do</em> rather than on its
 * underlying representation. Once it has been built, and regardless of its
 * internal representation, a rotation is an <em>operator</em> which basically
 * transforms three dimensional {@link Vector3D vectors} into other three
 * dimensional {@link Vector3D vectors}. Depending on the application, the
 * meaning of these vectors may vary and the semantics of the rotation also.</p>
 * <p>For example in an spacecraft attitude simulation tool, users will often
 * consider the vectors are fixed (say the Earth direction for example) and the
 * frames change. The rotation transforms the coordinates of the vector in inertial
 * frame into the coordinates of the same vector in satellite frame. In this
 * case, the rotation implicitly defines the relation between the two frames.</p>
 * <p>Another example could be a telescope control application, where the rotation
 * would transform the sighting direction at rest into the desired observing
 * direction when the telescope is pointed towards an object of interest. In this
 * case the rotation transforms the direction at rest in a topocentric frame
 * into the sighting direction in the same topocentric frame. This implies in this
 * case the frame is fixed and the vector moves.</p>
 * <p>In many case, both approaches will be combined. In our telescope example,
 * we will probably also need to transform the observing direction in the topocentric
 * frame into the observing direction in inertial frame taking into account the observatory
 * location and the Earth rotation, which would essentially be an application of the
 * first approach.</p>
 *
 * <p>These examples show that a rotation is what the user wants it to be. This
 * class does not push the user towards one specific definition and hence does not
 * provide methods like <code>projectVectorIntoDestinationFrame</code> or
 * <code>computeTransformedDirection</code>. It provides simpler and more generic
 * methods: {@link #applyTo(Vector3D) applyTo(Vector3D)} and {@link
 * #applyInverseTo(Vector3D) applyInverseTo(Vector3D)}.</p>
 *
 * <p>Since a rotation is basically a vectorial operator, several rotations can be
 * composed together and the composite operation <code>r = r<sub>1</sub> o
 * r<sub>2</sub></code> (which means that for each vector <code>u</code>,
 * <code>r(u) = r<sub>1</sub>(r<sub>2</sub>(u))</code>) is also a rotation. Hence
 * we can consider that in addition to vectors, a rotation can be applied to other
 * rotations as well (or to itself). With our previous notations, we would say we
 * can apply <code>r<sub>1</sub></code> to <code>r<sub>2</sub></code> and the result
 * we get is <code>r = r<sub>1</sub> o r<sub>2</sub></code>. For this purpose, the
 * class provides the methods: {@link #applyTo(Rotation) applyTo(Rotation)} and
 * {@link #applyInverseTo(Rotation) applyInverseTo(Rotation)}.</p>
 *
 * <p>Rotations are guaranteed to be immutable objects.</p>
 *
 * @see Vector3D
 * @see RotationOrder
 * @since 1.2
 */

public class Rotation implements Serializable {

  /** Identity rotation. */
  public static final Rotation IDENTITY = new Rotation(1.0, 0.0, 0.0, 0.0, false);

  /** Serializable version identifier */
  private static final long serialVersionUID = -2153622329907944313L;

  /** Scalar coordinate of the quaternion. */
  private final double q0;

  /** First coordinate of the vectorial part of the quaternion. */
  private final double q1;

  /** Second coordinate of the vectorial part of the quaternion. */
  private final double q2;

  /** Third coordinate of the vectorial part of the quaternion. */
  private final double q3;

  /** Build a rotation from the quaternion coordinates.
   * <p>A rotation can be built from a <em>normalized</em> quaternion,
   * i.e. a quaternion for which q<sub>0</sub><sup>2</sup> +
   * q<sub>1</sub><sup>2</sup> + q<sub>2</sub><sup>2</sup> +
   * q<sub>3</sub><sup>2</sup> = 1. If the quaternion is not normalized,
   * the constructor can normalize it in a preprocessing step.</p>
   * <p>Note that some conventions put the scalar part of the quaternion
   * as the 4<sup>th</sup> component and the vector part as the first three
   * components. This is <em>not</em> our convention. We put the scalar part
   * as the first component.</p>
   * @param q0 scalar part of the quaternion
   * @param q1 first coordinate of the vectorial part of the quaternion
   * @param q2 second coordinate of the vectorial part of the quaternion
   * @param q3 third coordinate of the vectorial part of the quaternion
   * @param needsNormalization if true, the coordinates are considered
   * not to be normalized, a normalization preprocessing step is performed
   * before using them
   */
  public Rotation(double q0, double q1, double q2, double q3,
                  boolean needsNormalization) {

    if (needsNormalization) {
      // normalization preprocessing
      double inv = 1.0 / FastMath.sqrt(q0 * q0 + q1 * q1 + q2 * q2 + q3 * q3);
      q0 *= inv;
      q1 *= inv;
      q2 *= inv;
      q3 *= inv;
    }

    this.q0 = q0;
    this.q1 = q1;
    this.q2 = q2;
    this.q3 = q3;

  }

  /** Build a rotation from an axis and an angle.
   * <p>
   * Calling this constructor is equivalent to call
   * {@link #Rotation(Vector3D, double, RotationConvention)
   * new Rotation(axis, angle, RotationConvention.VECTOR_OPERATOR)}
   * </p>
   * @param axis axis around which to rotate
   * @param angle rotation angle.
   * @exception MathIllegalArgumentException if the axis norm is zero
   * @deprecated as of 3.6, replaced with {@link #Rotation(Vector3D, double, RotationConvention)}
   */
  @Deprecated
  public Rotation(Vector3D axis, double angle) throws MathIllegalArgumentException {
      this(axis, angle, RotationConvention.VECTOR_OPERATOR);
  }

  /** Build a rotation from an axis and an angle.
   * @param axis axis around which to rotate
   * @param angle rotation angle
   * @param convention convention to use for the semantics of the angle
   * @exception MathIllegalArgumentException if the axis norm is zero
   * @since 3.6
   */
  public Rotation(final Vector3D axis, final double angle, final RotationConvention convention)
      throws MathIllegalArgumentException {

    double norm = axis.getNorm();
    if (norm == 0) {
      throw new MathIllegalArgumentException(LocalizedFormats.ZERO_NORM_FOR_ROTATION_AXIS);
    }

    double halfAngle = convention == RotationConvention.VECTOR_OPERATOR ? -0.5 * angle : +0.5 * angle;
    double coeff = FastMath.sin(halfAngle) / norm;

    q0 = FastMath.cos (halfAngle);
    q1 = coeff * axis.getX();
    q2 = coeff * axis.getY();
    q3 = coeff * axis.getZ();

  }

  /** Build a rotation from a 3X3 matrix.

   * <p>Rotation matrices are orthogonal matrices, i.e. unit matrices
   * (which are matrices for which m.m<sup>T</sup> = I) with real
   * coefficients. The module of the determinant of unit matrices is
   * 1, among the orthogonal 3X3 matrices, only the ones having a
   * positive determinant (+1) are rotation matrices.</p>

   * <p>When a rotation is defined by a matrix with truncated values
   * (typically when it is extracted from a technical sheet where only
   * four to five significant digits are available), the matrix is not
   * orthogonal anymore. This constructor handles this case
   * transparently by using a copy of the given matrix and applying a
   * correction to the copy in order to perfect its orthogonality. If
   * the Frobenius norm of the correction needed is above the given
   * threshold, then the matrix is considered to be too far from a
   * true rotation matrix and an exception is thrown.<p>

   * @param m rotation matrix
   * @param threshold convergence threshold for the iterative
   * orthogonality correction (convergence is reached when the
   * difference between two steps of the Frobenius norm of the
   * correction is below this threshold)

   * @exception NotARotationMatrixException if the matrix is not a 3X3
   * matrix, or if it cannot be transformed into an orthogonal matrix
   * with the given threshold, or if the determinant of the resulting
   * orthogonal matrix is negative

   */
  public Rotation(double[][] m, double threshold)
    throws NotARotationMatrixException {

    // dimension check
    if ((m.length != 3) || (m[0].length != 3) ||
        (m[1].length != 3) || (m[2].length != 3)) {
      throw new NotARotationMatrixException(
              LocalizedFormats.ROTATION_MATRIX_DIMENSIONS,
              m.length, m[0].length);
    }

    // compute a "close" orthogonal matrix
    double[][] ort = orthogonalizeMatrix(m, threshold);

    // check the sign of the determinant
    double det = ort[0][0] * (ort[1][1] * ort[2][2] - ort[2][1] * ort[1][2]) -
                 ort[1][0] * (ort[0][1] * ort[2][2] - ort[2][1] * ort[0][2]) +
                 ort[2][0] * (ort[0][1] * ort[1][2] - ort[1][1] * ort[0][2]);
    if (det < 0.0) {
      throw new NotARotationMatrixException(
              LocalizedFormats.CLOSEST_ORTHOGONAL_MATRIX_HAS_NEGATIVE_DETERMINANT,
              det);
    }

    double[] quat = mat2quat(ort);
    q0 = quat[0];
    q1 = quat[1];
    q2 = quat[2];
    q3 = quat[3];

  }

  /** Build the rotation that transforms a pair of vectors into another pair.

   * <p>Except for possible scale factors, if the instance were applied to
   * the pair (u<sub>1</sub>, u<sub>2</sub>) it will produce the pair
   * (v<sub>1</sub>, v<sub>2</sub>).</p>

   * <p>If the angular separation between u<sub>1</sub> and u<sub>2</sub> is
   * not the same as the angular separation between v<sub>1</sub> and
   * v<sub>2</sub>, then a corrected v'<sub>2</sub> will be used rather than
   * v<sub>2</sub>, the corrected vector will be in the (&pm;v<sub>1</sub>,
   * +v<sub>2</sub>) half-plane.</p>

   * @param u1 first vector of the origin pair
   * @param u2 second vector of the origin pair
   * @param v1 desired image of u1 by the rotation
   * @param v2 desired image of u2 by the rotation
   * @exception MathArithmeticException if the norm of one of the vectors is zero,
   * or if one of the pair is degenerated (i.e. the vectors of the pair are collinear)
   */
  public Rotation(Vector3D u1, Vector3D u2, Vector3D v1, Vector3D v2)
      throws MathArithmeticException {

      // build orthonormalized base from u1, u2
      // this fails when vectors are null or collinear, which is forbidden to define a rotation
      final Vector3D u3 = u1.crossProduct(u2).normalize();
      u2 = u3.crossProduct(u1).normalize();
      u1 = u1.normalize();

      // build an orthonormalized base from v1, v2
      // this fails when vectors are null or collinear, which is forbidden to define a rotation
      final Vector3D v3 = v1.crossProduct(v2).normalize();
      v2 = v3.crossProduct(v1).normalize();
      v1 = v1.normalize();

      // buid a matrix transforming the first base into the second one
      final double[][] m = new double[][] {
          {
              MathArrays.linearCombination(u1.getX(), v1.getX(), u2.getX(), v2.getX(), u3.getX(), v3.getX()),
              MathArrays.linearCombination(u1.getY(), v1.getX(), u2.getY(), v2.getX(), u3.getY(), v3.getX()),
              MathArrays.linearCombination(u1.getZ(), v1.getX(), u2.getZ(), v2.getX(), u3.getZ(), v3.getX())
          },
          {
              MathArrays.linearCombination(u1.getX(), v1.getY(), u2.getX(), v2.getY(), u3.getX(), v3.getY()),
              MathArrays.linearCombination(u1.getY(), v1.getY(), u2.getY(), v2.getY(), u3.getY(), v3.getY()),
              MathArrays.linearCombination(u1.getZ(), v1.getY(), u2.getZ(), v2.getY(), u3.getZ(), v3.getY())
          },
          {
              MathArrays.linearCombination(u1.getX(), v1.getZ(), u2.getX(), v2.getZ(), u3.getX(), v3.getZ()),
              MathArrays.linearCombination(u1.getY(), v1.getZ(), u2.getY(), v2.getZ(), u3.getY(), v3.getZ()),
              MathArrays.linearCombination(u1.getZ(), v1.getZ(), u2.getZ(), v2.getZ(), u3.getZ(), v3.getZ())
          }
      };

      double[] quat = mat2quat(m);
      q0 = quat[0];
      q1 = quat[1];
      q2 = quat[2];
      q3 = quat[3];

  }

  /** Build one of the rotations that transform one vector into another one.

   * <p>Except for a possible scale factor, if the instance were
   * applied to the vector u it will produce the vector v. There is an
   * infinite number of such rotations, this constructor choose the
   * one with the smallest associated angle (i.e. the one whose axis
   * is orthogonal to the (u, v) plane). If u and v are collinear, an
   * arbitrary rotation axis is chosen.</p>

   * @param u origin vector
   * @param v desired image of u by the rotation
   * @exception MathArithmeticException if the norm of one of the vectors is zero
   */
  public Rotation(Vector3D u, Vector3D v) throws MathArithmeticException {

    double normProduct = u.getNorm() * v.getNorm();
    if (normProduct == 0) {
        throw new MathArithmeticException(LocalizedFormats.ZERO_NORM_FOR_ROTATION_DEFINING_VECTOR);
    }

    double dot = u.dotProduct(v);

    if (dot < ((2.0e-15 - 1.0) * normProduct)) {
      // special case u = -v: we select a PI angle rotation around
      // an arbitrary vector orthogonal to u
      Vector3D w = u.orthogonal();
      q0 = 0.0;
      q1 = -w.getX();
      q2 = -w.getY();
      q3 = -w.getZ();
    } else {
      // general case: (u, v) defines a plane, we select
      // the shortest possible rotation: axis orthogonal to this plane
      q0 = FastMath.sqrt(0.5 * (1.0 + dot / normProduct));
      double coeff = 1.0 / (2.0 * q0 * normProduct);
      Vector3D q = v.crossProduct(u);
      q1 = coeff * q.getX();
      q2 = coeff * q.getY();
      q3 = coeff * q.getZ();
    }

  }

  /** Build a rotation from three Cardan or Euler elementary rotations.

   * <p>
   * Calling this constructor is equivalent to call
   * {@link #Rotation(RotationOrder, RotationConvention, double, double, double)
   * new Rotation(order, RotationConvention.VECTOR_OPERATOR, alpha1, alpha2, alpha3)}
   * </p>

   * @param order order of rotations to use
   * @param alpha1 angle of the first elementary rotation
   * @param alpha2 angle of the second elementary rotation
   * @param alpha3 angle of the third elementary rotation
   * @deprecated as of 3.6, replaced with {@link
   * #Rotation(RotationOrder, RotationConvention, double, double, double)}
   */
  @Deprecated
  public Rotation(RotationOrder order,
                  double alpha1, double alpha2, double alpha3) {
      this(order, RotationConvention.VECTOR_OPERATOR, alpha1, alpha2, alpha3);
  }

  /** Build a rotation from three Cardan or Euler elementary rotations.

   * <p>Cardan rotations are three successive rotations around the
   * canonical axes X, Y and Z, each axis being used once. There are
   * 6 such sets of rotations (XYZ, XZY, YXZ, YZX, ZXY and ZYX). Euler
   * rotations are three successive rotations around the canonical
   * axes X, Y and Z, the first and last rotations being around the
   * same axis. There are 6 such sets of rotations (XYX, XZX, YXY,
   * YZY, ZXZ and ZYZ), the most popular one being ZXZ.</p>
   * <p>Beware that many people routinely use the term Euler angles even
   * for what really are Cardan angles (this confusion is especially
   * widespread in the aerospace business where Roll, Pitch and Yaw angles
   * are often wrongly tagged as Euler angles).</p>

   * @param order order of rotations to compose, from left to right
   * (i.e. we will use {@code r1.compose(r2.compose(r3, convention), convention)})
   * @param convention convention to use for the semantics of the angle
   * @param alpha1 angle of the first elementary rotation
   * @param alpha2 angle of the second elementary rotation
   * @param alpha3 angle of the third elementary rotation
   * @since 3.6
   */
  public Rotation(RotationOrder order, RotationConvention convention,
                  double alpha1, double alpha2, double alpha3) {
      Rotation r1 = new Rotation(order.getA1(), alpha1, convention);
      Rotation r2 = new Rotation(order.getA2(), alpha2, convention);
      Rotation r3 = new Rotation(order.getA3(), alpha3, convention);
      Rotation composed = r1.compose(r2.compose(r3, convention), convention);
      q0 = composed.q0;
      q1 = composed.q1;
      q2 = composed.q2;
      q3 = composed.q3;
  }

  /** Convert an orthogonal rotation matrix to a quaternion.
   * @param ort orthogonal rotation matrix
   * @return quaternion corresponding to the matrix
   */
  private static double[] mat2quat(final double[][] ort) {

      final double[] quat = new double[4];

      // There are different ways to compute the quaternions elements
      // from the matrix. They all involve computing one element from
      // the diagonal of the matrix, and computing the three other ones
      // using a formula involving a division by the first element,
      // which unfortunately can be zero. Since the norm of the
      // quaternion is 1, we know at least one element has an absolute
      // value greater or equal to 0.5, so it is always possible to
      // select the right formula and avoid division by zero and even
      // numerical inaccuracy. Checking the elements in turn and using
      // the first one greater than 0.45 is safe (this leads to a simple
      // test since qi = 0.45 implies 4 qi^2 - 1 = -0.19)
      double s = ort[0][0] + ort[1][1] + ort[2][2];
      if (s > -0.19) {
          // compute q0 and deduce q1, q2 and q3
          quat[0] = 0.5 * FastMath.sqrt(s + 1.0);
          double inv = 0.25 / quat[0];
          quat[1] = inv * (ort[1][2] - ort[2][1]);
          quat[2] = inv * (ort[2][0] - ort[0][2]);
          quat[3] = inv * (ort[0][1] - ort[1][0]);
      } else {
          s = ort[0][0] - ort[1][1] - ort[2][2];
          if (s > -0.19) {
              // compute q1 and deduce q0, q2 and q3
              quat[1] = 0.5 * FastMath.sqrt(s + 1.0);
              double inv = 0.25 / quat[1];
              quat[0] = inv * (ort[1][2] - ort[2][1]);
              quat[2] = inv * (ort[0][1] + ort[1][0]);
              quat[3] = inv * (ort[0][2] + ort[2][0]);
          } else {
              s = ort[1][1] - ort[0][0] - ort[2][2];
              if (s > -0.19) {
                  // compute q2 and deduce q0, q1 and q3
                  quat[2] = 0.5 * FastMath.sqrt(s + 1.0);
                  double inv = 0.25 / quat[2];
                  quat[0] = inv * (ort[2][0] - ort[0][2]);
                  quat[1] = inv * (ort[0][1] + ort[1][0]);
                  quat[3] = inv * (ort[2][1] + ort[1][2]);
              } else {
                  // compute q3 and deduce q0, q1 and q2
                  s = ort[2][2] - ort[0][0] - ort[1][1];
                  quat[3] = 0.5 * FastMath.sqrt(s + 1.0);
                  double inv = 0.25 / quat[3];
                  quat[0] = inv * (ort[0][1] - ort[1][0]);
                  quat[1] = inv * (ort[0][2] + ort[2][0]);
                  quat[2] = inv * (ort[2][1] + ort[1][2]);
              }
          }
      }

      return quat;

  }

  /** Revert a rotation.
   * Build a rotation which reverse the effect of another
   * rotation. This means that if r(u) = v, then r.revert(v) = u. The
   * instance is not changed.
   * @return a new rotation whose effect is the reverse of the effect
   * of the instance
   */
  public Rotation revert() {
    return new Rotation(-q0, q1, q2, q3, false);
  }

  /** Get the scalar coordinate of the quaternion.
   * @return scalar coordinate of the quaternion
   */
  public double getQ0() {
    return q0;
  }

  /** Get the first coordinate of the vectorial part of the quaternion.
   * @return first coordinate of the vectorial part of the quaternion
   */
  public double getQ1() {
    return q1;
  }

  /** Get the second coordinate of the vectorial part of the quaternion.
   * @return second coordinate of the vectorial part of the quaternion
   */
  public double getQ2() {
    return q2;
  }

  /** Get the third coordinate of the vectorial part of the quaternion.
   * @return third coordinate of the vectorial part of the quaternion
   */
  public double getQ3() {
    return q3;
  }

  /** Get the normalized axis of the rotation.
   * <p>
   * Calling this method is equivalent to call
   * {@link #getAxis(RotationConvention) getAxis(RotationConvention.VECTOR_OPERATOR)}
   * </p>
   * @return normalized axis of the rotation
   * @see #Rotation(Vector3D, double, RotationConvention)
   * @deprecated as of 3.6, replaced with {@link #getAxis(RotationConvention)}
   */
  @Deprecated
  public Vector3D getAxis() {
    return getAxis(RotationConvention.VECTOR_OPERATOR);
  }

  /** Get the normalized axis of the rotation.
   * <p>
   * Note that as {@link #getAngle()} always returns an angle
   * between 0 and &pi;, changing the convention changes the
   * direction of the axis, not the sign of the angle.
   * </p>
   * @param convention convention to use for the semantics of the angle
   * @return normalized axis of the rotation
   * @see #Rotation(Vector3D, double, RotationConvention)
   * @since 3.6
   */
  public Vector3D getAxis(final RotationConvention convention) {
    final double squaredSine = q1 * q1 + q2 * q2 + q3 * q3;
    if (squaredSine == 0) {
      return convention == RotationConvention.VECTOR_OPERATOR ? Vector3D.PLUS_I : Vector3D.MINUS_I;
    } else {
        final double sgn = convention == RotationConvention.VECTOR_OPERATOR ? +1 : -1;
        if (q0 < 0) {
            final double inverse = sgn / FastMath.sqrt(squaredSine);
            return new Vector3D(q1 * inverse, q2 * inverse, q3 * inverse);
        }
        final double inverse = -sgn / FastMath.sqrt(squaredSine);
        return new Vector3D(q1 * inverse, q2 * inverse, q3 * inverse);
    }
  }

  /** Get the angle of the rotation.
   * @return angle of the rotation (between 0 and &pi;)
   * @see #Rotation(Vector3D, double)
   */
  public double getAngle() {
    if ((q0 < -0.1) || (q0 > 0.1)) {
      return 2 * FastMath.asin(FastMath.sqrt(q1 * q1 + q2 * q2 + q3 * q3));
    } else if (q0 < 0) {
      return 2 * FastMath.acos(-q0);
    }
    return 2 * FastMath.acos(q0);
  }

  /** Get the Cardan or Euler angles corresponding to the instance.

   * <p>
   * Calling this method is equivalent to call
   * {@link #getAngles(RotationOrder, RotationConvention)
   * getAngles(order, RotationConvention.VECTOR_OPERATOR)}
   * </p>

   * @param order rotation order to use
   * @return an array of three angles, in the order specified by the set
   * @exception CardanEulerSingularityException if the rotation is
   * singular with respect to the angles set specified
   * @deprecated as of 3.6, replaced with {@link #getAngles(RotationOrder, RotationConvention)}
   */
  @Deprecated
  public double[] getAngles(RotationOrder order)
      throws CardanEulerSingularityException {
      return getAngles(order, RotationConvention.VECTOR_OPERATOR);
  }

  /** Get the Cardan or Euler angles corresponding to the instance.

   * <p>The equations show that each rotation can be defined by two
   * different values of the Cardan or Euler angles set. For example
   * if Cardan angles are used, the rotation defined by the angles
   * a<sub>1</sub>, a<sub>2</sub> and a<sub>3</sub> is the same as
   * the rotation defined by the angles &pi; + a<sub>1</sub>, &pi;
   * - a<sub>2</sub> and &pi; + a<sub>3</sub>. This method implements
   * the following arbitrary choices:</p>
   * <ul>
   *   <li>for Cardan angles, the chosen set is the one for which the
   *   second angle is between -&pi;/2 and &pi;/2 (i.e its cosine is
   *   positive),</li>
   *   <li>for Euler angles, the chosen set is the one for which the
   *   second angle is between 0 and &pi; (i.e its sine is positive).</li>
   * </ul>

   * <p>Cardan and Euler angle have a very disappointing drawback: all
   * of them have singularities. This means that if the instance is
   * too close to the singularities corresponding to the given
   * rotation order, it will be impossible to retrieve the angles. For
   * Cardan angles, this is often called gimbal lock. There is
   * <em>nothing</em> to do to prevent this, it is an intrinsic problem
   * with Cardan and Euler representation (but not a problem with the
   * rotation itself, which is perfectly well defined). For Cardan
   * angles, singularities occur when the second angle is close to
   * -&pi;/2 or +&pi;/2, for Euler angle singularities occur when the
   * second angle is close to 0 or &pi;, this implies that the identity
   * rotation is always singular for Euler angles!</p>

   * @param order rotation order to use
   * @param convention convention to use for the semantics of the angle
   * @return an array of three angles, in the order specified by the set
   * @exception CardanEulerSingularityException if the rotation is
   * singular with respect to the angles set specified
   * @since 3.6
   */
  public double[] getAngles(RotationOrder order, RotationConvention convention)
      throws CardanEulerSingularityException {

      if (convention == RotationConvention.VECTOR_OPERATOR) {
          if (order == RotationOrder.XYZ) {

              // r (Vector3D.plusK) coordinates are :
              //  sin (theta), -cos (theta) sin (phi), cos (theta) cos (phi)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (psi) cos (theta), -sin (psi) cos (theta), sin (theta)
              // and we can choose to have theta in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if  ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(-(v1.getY()), v1.getZ()),
                  FastMath.asin(v2.getZ()),
                  FastMath.atan2(-(v2.getY()), v2.getX())
              };

          } else if (order == RotationOrder.XZY) {

              // r (Vector3D.plusJ) coordinates are :
              // -sin (psi), cos (psi) cos (phi), cos (psi) sin (phi)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (theta) cos (psi), -sin (psi), sin (theta) cos (psi)
              // and we can choose to have psi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(v1.getZ(), v1.getY()),
                 -FastMath.asin(v2.getY()),
                  FastMath.atan2(v2.getZ(), v2.getX())
              };

          } else if (order == RotationOrder.YXZ) {

              // r (Vector3D.plusK) coordinates are :
              //  cos (phi) sin (theta), -sin (phi), cos (phi) cos (theta)
              // (-r) (Vector3D.plusJ) coordinates are :
              // sin (psi) cos (phi), cos (psi) cos (phi), -sin (phi)
              // and we can choose to have phi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(v1.getX(), v1.getZ()),
                 -FastMath.asin(v2.getZ()),
                  FastMath.atan2(v2.getX(), v2.getY())
              };

          } else if (order == RotationOrder.YZX) {

              // r (Vector3D.plusI) coordinates are :
              // cos (psi) cos (theta), sin (psi), -cos (psi) sin (theta)
              // (-r) (Vector3D.plusJ) coordinates are :
              // sin (psi), cos (phi) cos (psi), -sin (phi) cos (psi)
              // and we can choose to have psi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(-(v1.getZ()), v1.getX()),
                  FastMath.asin(v2.getX()),
                  FastMath.atan2(-(v2.getZ()), v2.getY())
              };

          } else if (order == RotationOrder.ZXY) {

              // r (Vector3D.plusJ) coordinates are :
              // -cos (phi) sin (psi), cos (phi) cos (psi), sin (phi)
              // (-r) (Vector3D.plusK) coordinates are :
              // -sin (theta) cos (phi), sin (phi), cos (theta) cos (phi)
              // and we can choose to have phi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(-(v1.getX()), v1.getY()),
                  FastMath.asin(v2.getY()),
                  FastMath.atan2(-(v2.getX()), v2.getZ())
              };

          } else if (order == RotationOrder.ZYX) {

              // r (Vector3D.plusI) coordinates are :
              //  cos (theta) cos (psi), cos (theta) sin (psi), -sin (theta)
              // (-r) (Vector3D.plusK) coordinates are :
              // -sin (theta), sin (phi) cos (theta), cos (phi) cos (theta)
              // and we can choose to have theta in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(v1.getY(), v1.getX()),
                 -FastMath.asin(v2.getX()),
                  FastMath.atan2(v2.getY(), v2.getZ())
              };

          } else if (order == RotationOrder.XYX) {

              // r (Vector3D.plusI) coordinates are :
              //  cos (theta), sin (phi1) sin (theta), -cos (phi1) sin (theta)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (theta), sin (theta) sin (phi2), sin (theta) cos (phi2)
              // and we can choose to have theta in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v1.getY(), -v1.getZ()),
                  FastMath.acos(v2.getX()),
                  FastMath.atan2(v2.getY(), v2.getZ())
              };

          } else if (order == RotationOrder.XZX) {

              // r (Vector3D.plusI) coordinates are :
              //  cos (psi), cos (phi1) sin (psi), sin (phi1) sin (psi)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (psi), -sin (psi) cos (phi2), sin (psi) sin (phi2)
              // and we can choose to have psi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v1.getZ(), v1.getY()),
                  FastMath.acos(v2.getX()),
                  FastMath.atan2(v2.getZ(), -v2.getY())
              };

          } else if (order == RotationOrder.YXY) {

              // r (Vector3D.plusJ) coordinates are :
              //  sin (theta1) sin (phi), cos (phi), cos (theta1) sin (phi)
              // (-r) (Vector3D.plusJ) coordinates are :
              // sin (phi) sin (theta2), cos (phi), -sin (phi) cos (theta2)
              // and we can choose to have phi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v1.getX(), v1.getZ()),
                  FastMath.acos(v2.getY()),
                  FastMath.atan2(v2.getX(), -v2.getZ())
              };

          } else if (order == RotationOrder.YZY) {

              // r (Vector3D.plusJ) coordinates are :
              //  -cos (theta1) sin (psi), cos (psi), sin (theta1) sin (psi)
              // (-r) (Vector3D.plusJ) coordinates are :
              // sin (psi) cos (theta2), cos (psi), sin (psi) sin (theta2)
              // and we can choose to have psi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v1.getZ(), -v1.getX()),
                  FastMath.acos(v2.getY()),
                  FastMath.atan2(v2.getZ(), v2.getX())
              };

          } else if (order == RotationOrder.ZXZ) {

              // r (Vector3D.plusK) coordinates are :
              //  sin (psi1) sin (phi), -cos (psi1) sin (phi), cos (phi)
              // (-r) (Vector3D.plusK) coordinates are :
              // sin (phi) sin (psi2), sin (phi) cos (psi2), cos (phi)
              // and we can choose to have phi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v1.getX(), -v1.getY()),
                  FastMath.acos(v2.getZ()),
                  FastMath.atan2(v2.getX(), v2.getY())
              };

          } else { // last possibility is ZYZ

              // r (Vector3D.plusK) coordinates are :
              //  cos (psi1) sin (theta), sin (psi1) sin (theta), cos (theta)
              // (-r) (Vector3D.plusK) coordinates are :
              // -sin (theta) cos (psi2), sin (theta) sin (psi2), cos (theta)
              // and we can choose to have theta in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v1.getY(), v1.getX()),
                  FastMath.acos(v2.getZ()),
                  FastMath.atan2(v2.getY(), -v2.getX())
              };

          }
      } else {
          if (order == RotationOrder.XYZ) {

              // r (Vector3D.plusI) coordinates are :
              //  cos (theta) cos (psi), -cos (theta) sin (psi), sin (theta)
              // (-r) (Vector3D.plusK) coordinates are :
              // sin (theta), -sin (phi) cos (theta), cos (phi) cos (theta)
              // and we can choose to have theta in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(-v2.getY(), v2.getZ()),
                  FastMath.asin(v2.getX()),
                  FastMath.atan2(-v1.getY(), v1.getX())
              };

          } else if (order == RotationOrder.XZY) {

              // r (Vector3D.plusI) coordinates are :
              // cos (psi) cos (theta), -sin (psi), cos (psi) sin (theta)
              // (-r) (Vector3D.plusJ) coordinates are :
              // -sin (psi), cos (phi) cos (psi), sin (phi) cos (psi)
              // and we can choose to have psi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(v2.getZ(), v2.getY()),
                 -FastMath.asin(v2.getX()),
                  FastMath.atan2(v1.getZ(), v1.getX())
              };

          } else if (order == RotationOrder.YXZ) {

              // r (Vector3D.plusJ) coordinates are :
              // cos (phi) sin (psi), cos (phi) cos (psi), -sin (phi)
              // (-r) (Vector3D.plusK) coordinates are :
              // sin (theta) cos (phi), -sin (phi), cos (theta) cos (phi)
              // and we can choose to have phi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(v2.getX(), v2.getZ()),
                 -FastMath.asin(v2.getY()),
                  FastMath.atan2(v1.getX(), v1.getY())
              };

          } else if (order == RotationOrder.YZX) {

              // r (Vector3D.plusJ) coordinates are :
              // sin (psi), cos (psi) cos (phi), -cos (psi) sin (phi)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (theta) cos (psi), sin (psi), -sin (theta) cos (psi)
              // and we can choose to have psi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(-v2.getZ(), v2.getX()),
                  FastMath.asin(v2.getY()),
                  FastMath.atan2(-v1.getZ(), v1.getY())
              };

          } else if (order == RotationOrder.ZXY) {

              // r (Vector3D.plusK) coordinates are :
              //  -cos (phi) sin (theta), sin (phi), cos (phi) cos (theta)
              // (-r) (Vector3D.plusJ) coordinates are :
              // -sin (psi) cos (phi), cos (psi) cos (phi), sin (phi)
              // and we can choose to have phi in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(-v2.getX(), v2.getY()),
                  FastMath.asin(v2.getZ()),
                  FastMath.atan2(-v1.getX(), v1.getZ())
              };

          } else if (order == RotationOrder.ZYX) {

              // r (Vector3D.plusK) coordinates are :
              //  -sin (theta), cos (theta) sin (phi), cos (theta) cos (phi)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (psi) cos (theta), sin (psi) cos (theta), -sin (theta)
              // and we can choose to have theta in the interval [-PI/2 ; +PI/2]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if  ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(true);
              }
              return new double[] {
                  FastMath.atan2(v2.getY(), v2.getX()),
                 -FastMath.asin(v2.getZ()),
                  FastMath.atan2(v1.getY(), v1.getZ())
              };

          } else if (order == RotationOrder.XYX) {

              // r (Vector3D.plusI) coordinates are :
              //  cos (theta), sin (phi2) sin (theta), cos (phi2) sin (theta)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (theta), sin (theta) sin (phi1), -sin (theta) cos (phi1)
              // and we can choose to have theta in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v2.getY(), -v2.getZ()),
                  FastMath.acos(v2.getX()),
                  FastMath.atan2(v1.getY(), v1.getZ())
              };

          } else if (order == RotationOrder.XZX) {

              // r (Vector3D.plusI) coordinates are :
              //  cos (psi), -cos (phi2) sin (psi), sin (phi2) sin (psi)
              // (-r) (Vector3D.plusI) coordinates are :
              // cos (psi), sin (psi) cos (phi1), sin (psi) sin (phi1)
              // and we can choose to have psi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_I);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_I);
              if ((v2.getX() < -0.9999999999) || (v2.getX() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v2.getZ(), v2.getY()),
                  FastMath.acos(v2.getX()),
                  FastMath.atan2(v1.getZ(), -v1.getY())
              };

          } else if (order == RotationOrder.YXY) {

              // r (Vector3D.plusJ) coordinates are :
              // sin (phi) sin (theta2), cos (phi), -sin (phi) cos (theta2)
              // (-r) (Vector3D.plusJ) coordinates are :
              //  sin (theta1) sin (phi), cos (phi), cos (theta1) sin (phi)
              // and we can choose to have phi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v2.getX(), v2.getZ()),
                  FastMath.acos(v2.getY()),
                  FastMath.atan2(v1.getX(), -v1.getZ())
              };

          } else if (order == RotationOrder.YZY) {

              // r (Vector3D.plusJ) coordinates are :
              // sin (psi) cos (theta2), cos (psi), sin (psi) sin (theta2)
              // (-r) (Vector3D.plusJ) coordinates are :
              //  -cos (theta1) sin (psi), cos (psi), sin (theta1) sin (psi)
              // and we can choose to have psi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_J);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_J);
              if ((v2.getY() < -0.9999999999) || (v2.getY() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v2.getZ(), -v2.getX()),
                  FastMath.acos(v2.getY()),
                  FastMath.atan2(v1.getZ(), v1.getX())
              };

          } else if (order == RotationOrder.ZXZ) {

              // r (Vector3D.plusK) coordinates are :
              // sin (phi) sin (psi2), sin (phi) cos (psi2), cos (phi)
              // (-r) (Vector3D.plusK) coordinates are :
              //  sin (psi1) sin (phi), -cos (psi1) sin (phi), cos (phi)
              // and we can choose to have phi in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v2.getX(), -v2.getY()),
                  FastMath.acos(v2.getZ()),
                  FastMath.atan2(v1.getX(), v1.getY())
              };

          } else { // last possibility is ZYZ

              // r (Vector3D.plusK) coordinates are :
              // -sin (theta) cos (psi2), sin (theta) sin (psi2), cos (theta)
              // (-r) (Vector3D.plusK) coordinates are :
              //  cos (psi1) sin (theta), sin (psi1) sin (theta), cos (theta)
              // and we can choose to have theta in the interval [0 ; PI]
              Vector3D v1 = applyTo(Vector3D.PLUS_K);
              Vector3D v2 = applyInverseTo(Vector3D.PLUS_K);
              if ((v2.getZ() < -0.9999999999) || (v2.getZ() > 0.9999999999)) {
                  throw new CardanEulerSingularityException(false);
              }
              return new double[] {
                  FastMath.atan2(v2.getY(), v2.getX()),
                  FastMath.acos(v2.getZ()),
                  FastMath.atan2(v1.getY(), -v1.getX())
              };

          }
      }

  }

  /** Get the 3X3 matrix corresponding to the instance
   * @return the matrix corresponding to the instance
   */
  public double[][] getMatrix() {

    // products
    double q0q0  = q0 * q0;
    double q0q1  = q0 * q1;
    double q0q2  = q0 * q2;
    double q0q3  = q0 * q3;
    double q1q1  = q1 * q1;
    double q1q2  = q1 * q2;
    double q1q3  = q1 * q3;
    double q2q2  = q2 * q2;
    double q2q3  = q2 * q3;
    double q3q3  = q3 * q3;

    // create the matrix
    double[][] m = new double[3][];
    m[0] = new double[3];
    m[1] = new double[3];
    m[2] = new double[3];

    m [0][0] = 2.0 * (q0q0 + q1q1) - 1.0;
    m [1][0] = 2.0 * (q1q2 - q0q3);
    m [2][0] = 2.0 * (q1q3 + q0q2);

    m [0][1] = 2.0 * (q1q2 + q0q3);
    m [1][1] = 2.0 * (q0q0 + q2q2) - 1.0;
    m [2][1] = 2.0 * (q2q3 - q0q1);

    m [0][2] = 2.0 * (q1q3 - q0q2);
    m [1][2] = 2.0 * (q2q3 + q0q1);
    m [2][2] = 2.0 * (q0q0 + q3q3) - 1.0;

    return m;

  }

  /** Apply the rotation to a vector.
   * @param u vector to apply the rotation to
   * @return a new vector which is the image of u by the rotation
   */
  public Vector3D applyTo(Vector3D u) {

    double x = u.getX();
    double y = u.getY();
    double z = u.getZ();

    double s = q1 * x + q2 * y + q3 * z;

    return new Vector3D(2 * (q0 * (x * q0 - (q2 * z - q3 * y)) + s * q1) - x,
                        2 * (q0 * (y * q0 - (q3 * x - q1 * z)) + s * q2) - y,
                        2 * (q0 * (z * q0 - (q1 * y - q2 * x)) + s * q3) - z);

  }

  /** Apply the rotation to a vector stored in an array.
   * @param in an array with three items which stores vector to rotate
   * @param out an array with three items to put result to (it can be the same
   * array as in)
   */
  public void applyTo(final double[] in, final double[] out) {

      final double x = in[0];
      final double y = in[1];
      final double z = in[2];

      final double s = q1 * x + q2 * y + q3 * z;

      out[0] = 2 * (q0 * (x * q0 - (q2 * z - q3 * y)) + s * q1) - x;
      out[1] = 2 * (q0 * (y * q0 - (q3 * x - q1 * z)) + s * q2) - y;
      out[2] = 2 * (q0 * (z * q0 - (q1 * y - q2 * x)) + s * q3) - z;

  }

  /** Apply the inverse of the rotation to a vector.
   * @param u vector to apply the inverse of the rotation to
   * @return a new vector which such that u is its image by the rotation
   */
  public Vector3D applyInverseTo(Vector3D u) {

    double x = u.getX();
    double y = u.getY();
    double z = u.getZ();

    double s = q1 * x + q2 * y + q3 * z;
    double m0 = -q0;

    return new Vector3D(2 * (m0 * (x * m0 - (q2 * z - q3 * y)) + s * q1) - x,
                        2 * (m0 * (y * m0 - (q3 * x - q1 * z)) + s * q2) - y,
                        2 * (m0 * (z * m0 - (q1 * y - q2 * x)) + s * q3) - z);

  }

  /** Apply the inverse of the rotation to a vector stored in an array.
   * @param in an array with three items which stores vector to rotate
   * @param out an array with three items to put result to (it can be the same
   * array as in)
   */
  public void applyInverseTo(final double[] in, final double[] out) {

      final double x = in[0];
      final double y = in[1];
      final double z = in[2];

      final double s = q1 * x + q2 * y + q3 * z;
      final double m0 = -q0;

      out[0] = 2 * (m0 * (x * m0 - (q2 * z - q3 * y)) + s * q1) - x;
      out[1] = 2 * (m0 * (y * m0 - (q3 * x - q1 * z)) + s * q2) - y;
      out[2] = 2 * (m0 * (z * m0 - (q1 * y - q2 * x)) + s * q3) - z;

  }

  /** Apply the instance to another rotation.
   * <p>
   * Calling this method is equivalent to call
   * {@link #compose(Rotation, RotationConvention)
   * compose(r, RotationConvention.VECTOR_OPERATOR)}.
   * </p>
   * @param r rotation to apply the rotation to
   * @return a new rotation which is the composition of r by the instance
   */
  public Rotation applyTo(Rotation r) {
    return compose(r, RotationConvention.VECTOR_OPERATOR);
  }

  /** Compose the instance with another rotation.
   * <p>
   * If the semantics of the rotations composition corresponds to a
   * {@link RotationConvention#VECTOR_OPERATOR vector operator} convention,
   * applying the instance to a rotation is computing the composition
   * in an order compliant with the following rule : let {@code u} be any
   * vector and {@code v} its image by {@code r1} (i.e.
   * {@code r1.applyTo(u) = v}). Let {@code w} be the image of {@code v} by
   * rotation {@code r2} (i.e. {@code r2.applyTo(v) = w}). Then
   * {@code w = comp.applyTo(u)}, where
   * {@code comp = r2.compose(r1, RotationConvention.VECTOR_OPERATOR)}.
   * </p>
   * <p>
   * If the semantics of the rotations composition corresponds to a
   * {@link RotationConvention#FRAME_TRANSFORM frame transform} convention,
   * the application order will be reversed. So keeping the exact same
   * meaning of all {@code r1}, {@code r2}, {@code u}, {@code v}, {@code w}
   * and  {@code comp} as above, {@code comp} could also be computed as
   * {@code comp = r1.compose(r2, RotationConvention.FRAME_TRANSFORM)}.
   * </p>
   * @param r rotation to apply the rotation to
   * @param convention convention to use for the semantics of the angle
   * @return a new rotation which is the composition of r by the instance
   */
  public Rotation compose(final Rotation r, final RotationConvention convention) {
    return convention == RotationConvention.VECTOR_OPERATOR ?
           composeInternal(r) : r.composeInternal(this);
  }

  /** Compose the instance with another rotation using vector operator convention.
   * @param r rotation to apply the rotation to
   * @return a new rotation which is the composition of r by the instance
   * using vector operator convention
   */
  private Rotation composeInternal(final Rotation r) {
    return new Rotation(r.q0 * q0 - (r.q1 * q1 + r.q2 * q2 + r.q3 * q3),
                        r.q1 * q0 + r.q0 * q1 + (r.q2 * q3 - r.q3 * q2),
                        r.q2 * q0 + r.q0 * q2 + (r.q3 * q1 - r.q1 * q3),
                        r.q3 * q0 + r.q0 * q3 + (r.q1 * q2 - r.q2 * q1),
                        false);
  }

  /** Apply the inverse of the instance to another rotation.
   * <p>
   * Calling this method is equivalent to call
   * {@link #composeInverse(Rotation, RotationConvention)
   * composeInverse(r, RotationConvention.VECTOR_OPERATOR)}.
   * </p>
   * @param r rotation to apply the rotation to
   * @return a new rotation which is the composition of r by the inverse
   * of the instance
   */
  public Rotation applyInverseTo(Rotation r) {
    return composeInverse(r, RotationConvention.VECTOR_OPERATOR);
  }

  /** Compose the inverse of the instance with another rotation.
   * <p>
   * If the semantics of the rotations composition corresponds to a
   * {@link RotationConvention#VECTOR_OPERATOR vector operator} convention,
   * applying the inverse of the instance to a rotation is computing
   * the composition in an order compliant with the following rule :
   * let {@code u} be any vector and {@code v} its image by {@code r1}
   * (i.e. {@code r1.applyTo(u) = v}). Let {@code w} be the inverse image
   * of {@code v} by {@code r2} (i.e. {@code r2.applyInverseTo(v) = w}).
   * Then {@code w = comp.applyTo(u)}, where
   * {@code comp = r2.composeInverse(r1)}.
   * </p>
   * <p>
   * If the semantics of the rotations composition corresponds to a
   * {@link RotationConvention#FRAME_TRANSFORM frame transform} convention,
   * the application order will be reversed, which means it is the
   * <em>innermost</em> rotation that will be reversed. So keeping the exact same
   * meaning of all {@code r1}, {@code r2}, {@code u}, {@code v}, {@code w}
   * and  {@code comp} as above, {@code comp} could also be computed as
   * {@code comp = r1.revert().composeInverse(r2.revert(), RotationConvention.FRAME_TRANSFORM)}.
   * </p>
   * @param r rotation to apply the rotation to
   * @param convention convention to use for the semantics of the angle
   * @return a new rotation which is the composition of r by the inverse
   * of the instance
   */
  public Rotation composeInverse(final Rotation r, final RotationConvention convention) {
    return convention == RotationConvention.VECTOR_OPERATOR ?
           composeInverseInternal(r) : r.composeInternal(revert());
  }

  /** Compose the inverse of the instance with another rotation
   * using vector operator convention.
   * @param r rotation to apply the rotation to
   * @return a new rotation which is the composition of r by the inverse
   * of the instance using vector operator convention
   */
  private Rotation composeInverseInternal(Rotation r) {
    return new Rotation(-r.q0 * q0 - (r.q1 * q1 + r.q2 * q2 + r.q3 * q3),
                        -r.q1 * q0 + r.q0 * q1 + (r.q2 * q3 - r.q3 * q2),
                        -r.q2 * q0 + r.q0 * q2 + (r.q3 * q1 - r.q1 * q3),
                        -r.q3 * q0 + r.q0 * q3 + (r.q1 * q2 - r.q2 * q1),
                        false);
  }

  /** Perfect orthogonality on a 3X3 matrix.
   * @param m initial matrix (not exactly orthogonal)
   * @param threshold convergence threshold for the iterative
   * orthogonality correction (convergence is reached when the
   * difference between two steps of the Frobenius norm of the
   * correction is below this threshold)
   * @return an orthogonal matrix close to m
   * @exception NotARotationMatrixException if the matrix cannot be
   * orthogonalized with the given threshold after 10 iterations
   */
  private double[][] orthogonalizeMatrix(double[][] m, double threshold)
    throws NotARotationMatrixException {
    double[] m0 = m[0];
    double[] m1 = m[1];
    double[] m2 = m[2];
    double x00 = m0[0];
    double x01 = m0[1];
    double x02 = m0[2];
    double x10 = m1[0];
    double x11 = m1[1];
    double x12 = m1[2];
    double x20 = m2[0];
    double x21 = m2[1];
    double x22 = m2[2];
    double fn = 0;
    double fn1;

    double[][] o = new double[3][3];
    double[] o0 = o[0];
    double[] o1 = o[1];
    double[] o2 = o[2];

    // iterative correction: Xn+1 = Xn - 0.5 * (Xn.Mt.Xn - M)
    int i = 0;
    while (++i < 11) {

      // Mt.Xn
      double mx00 = m0[0] * x00 + m1[0] * x10 + m2[0] * x20;
      double mx10 = m0[1] * x00 + m1[1] * x10 + m2[1] * x20;
      double mx20 = m0[2] * x00 + m1[2] * x10 + m2[2] * x20;
      double mx01 = m0[0] * x01 + m1[0] * x11 + m2[0] * x21;
      double mx11 = m0[1] * x01 + m1[1] * x11 + m2[1] * x21;
      double mx21 = m0[2] * x01 + m1[2] * x11 + m2[2] * x21;
      double mx02 = m0[0] * x02 + m1[0] * x12 + m2[0] * x22;
      double mx12 = m0[1] * x02 + m1[1] * x12 + m2[1] * x22;
      double mx22 = m0[2] * x02 + m1[2] * x12 + m2[2] * x22;

      // Xn+1
      o0[0] = x00 - 0.5 * (x00 * mx00 + x01 * mx10 + x02 * mx20 - m0[0]);
      o0[1] = x01 - 0.5 * (x00 * mx01 + x01 * mx11 + x02 * mx21 - m0[1]);
      o0[2] = x02 - 0.5 * (x00 * mx02 + x01 * mx12 + x02 * mx22 - m0[2]);
      o1[0] = x10 - 0.5 * (x10 * mx00 + x11 * mx10 + x12 * mx20 - m1[0]);
      o1[1] = x11 - 0.5 * (x10 * mx01 + x11 * mx11 + x12 * mx21 - m1[1]);
      o1[2] = x12 - 0.5 * (x10 * mx02 + x11 * mx12 + x12 * mx22 - m1[2]);
      o2[0] = x20 - 0.5 * (x20 * mx00 + x21 * mx10 + x22 * mx20 - m2[0]);
      o2[1] = x21 - 0.5 * (x20 * mx01 + x21 * mx11 + x22 * mx21 - m2[1]);
      o2[2] = x22 - 0.5 * (x20 * mx02 + x21 * mx12 + x22 * mx22 - m2[2]);

      // correction on each elements
      double corr00 = o0[0] - m0[0];
      double corr01 = o0[1] - m0[1];
      double corr02 = o0[2] - m0[2];
      double corr10 = o1[0] - m1[0];
      double corr11 = o1[1] - m1[1];
      double corr12 = o1[2] - m1[2];
      double corr20 = o2[0] - m2[0];
      double corr21 = o2[1] - m2[1];
      double corr22 = o2[2] - m2[2];

      // Frobenius norm of the correction
      fn1 = corr00 * corr00 + corr01 * corr01 + corr02 * corr02 +
            corr10 * corr10 + corr11 * corr11 + corr12 * corr12 +
            corr20 * corr20 + corr21 * corr21 + corr22 * corr22;

      // convergence test
      if (FastMath.abs(fn1 - fn) <= threshold) {
          return o;
      }

      // prepare next iteration
      x00 = o0[0];
      x01 = o0[1];
      x02 = o0[2];
      x10 = o1[0];
      x11 = o1[1];
      x12 = o1[2];
      x20 = o2[0];
      x21 = o2[1];
      x22 = o2[2];
      fn  = fn1;

    }

    // the algorithm did not converge after 10 iterations
    throw new NotARotationMatrixException(
            LocalizedFormats.UNABLE_TO_ORTHOGONOLIZE_MATRIX,
            i - 1);
  }

  /** Compute the <i>distance</i> between two rotations.
   * <p>The <i>distance</i> is intended here as a way to check if two
   * rotations are almost similar (i.e. they transform vectors the same way)
   * or very different. It is mathematically defined as the angle of
   * the rotation r that prepended to one of the rotations gives the other
   * one:</p>
   * <pre>
   *        r<sub>1</sub>(r) = r<sub>2</sub>
   * </pre>
   * <p>This distance is an angle between 0 and &pi;. Its value is the smallest
   * possible upper bound of the angle in radians between r<sub>1</sub>(v)
   * and r<sub>2</sub>(v) for all possible vectors v. This upper bound is
   * reached for some v. The distance is equal to 0 if and only if the two
   * rotations are identical.</p>
   * <p>Comparing two rotations should always be done using this value rather
   * than for example comparing the components of the quaternions. It is much
   * more stable, and has a geometric meaning. Also comparing quaternions
   * components is error prone since for example quaternions (0.36, 0.48, -0.48, -0.64)
   * and (-0.36, -0.48, 0.48, 0.64) represent exactly the same rotation despite
   * their components are different (they are exact opposites).</p>
   * @param r1 first rotation
   * @param r2 second rotation
   * @return <i>distance</i> between r1 and r2
   */
  public static double distance(Rotation r1, Rotation r2) {
      return r1.composeInverseInternal(r2).getAngle();
  }

}
