package object;


/**
 *
 * @author christoph
 */
public class Naumann {
    Node[] m_result;

    /*@ determines  m_result,
                    (\seq_def int i; 0; m_result.length; m_result[i]),
                    (\seq_def int i; 0; m_result.length; m_result[i].val)
               \by  x;
     */
    //@ helper
    void  Pair_m(int x, int secret) {
        /*@ normal_behavior
            ensures     m_result != null && m_result.length == 10;
            ensures     \typeof(m_result) == \type(Node[]);
            determines      m_result \by \nothing
              \new_objects  m_result; */
        { m_result = new Node[10]; }
        int i = 0;
        /*@ loop_invariant 0 <= i && i <= m_result.length && m_result.length == 10;
            loop_invariant m_result != null && \typeof(m_result) == \type(Node[]);
            assignable  m_result[*];
            decreases   m_result.length - i;
            determines      i, x,
                            m_result,
                            (\seq_def int j; 0; i; m_result[j]),
                            (\seq_def int j; 0; i; m_result[j].val)
                   \by      \itself
              \new_objects  m_result[i-1];
          @*/
        while (i < 10) {
            m_result[i] = new Node();
            m_result[i].val = x;
            i++;
        }
    }

    class Node {
        public int val;
    }

}
