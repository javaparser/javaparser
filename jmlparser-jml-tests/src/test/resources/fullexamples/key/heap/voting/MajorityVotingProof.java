class MajorityVoting {
    /** number of voters */
    int V;

    /** number of candidates */
    int C;

    /**
     * @param votes array of size V containing the preferred candidate of
     *              each voter
     * @return the candidate number of the winner of the election if one
     *         exists, 0 otherwise
     */

    /**
     * Vorbedingungen: - es wird mind. 1 Stimme abgegeben
     *                 - die Stimmen werden für gueltige Kandidaten abgegeben
     *                 - V passt zum übergebenen Array
     *
     * Nachbedingungen: - das Ergebnis beschreibt einen gueltigen Kandidaten
     *                  - jeder Kandidat vereint hoechstens so viele Stimmen auf sich wie der Gewinner
     */

    /*@ public normal_behaviour
     @      requires (votes != null);
     @      requires (1 <= votes.length);
     @      requires (votes.length == V);
     @      requires (C >= 1);
     @      requires (\forall int a; 0 <= a && a < votes.length; 1 <= votes[a] && votes[a] <= C);
     @      assignable \nothing;
     @      ensures (1 <= \result && \result <= C);
     @      ensures (\forall int a; 1 <= a && a <= C; ((\sum int b; 0 <= b && b < votes.length; votes[b] == a ? 1 : 0) <= (\sum int c; 0 <= c && c < votes.length ; votes[c] == \result ? 1 : 0)));
     @*/
    int majorityVoting(int[] votes) {
        int[] res = new int[C+1];
        int i = 0;

        /**
         * Schleifeninvariante: - i liegt im gueltigen Bereich
         *                      - res enthaelt für jeden Kandidaten die Zahl an bisher ausgezaehlten Stimmen, die dieser Kandidaten auf sich vereint
         */

        /*@ loop_invariant
         @      0 <= i && i <= V && (\forall int a; 0 <= a && a < res.length; (\sum int b; 0 <= b && b < i ; votes[b] == a ? 1:0) == res[a]);
         @      assignable res[*];
         @      decreases V - i;
         @*/
        while(i < V) {
            res[votes[i]]++;
            i++;
        }

        //Vereinfachung: elect soll zwischen 1 und C liegen; initialisiere max mit res[i] (und nicht mit 0) um Invariante res[elect] = max zu garantieren
        //int max = 0;
        //int elect = 0;
        int max = res[1];
        int elect = 1;
        i = 1;

        /**
         * Schleifeninvariante: - i liegt im gueltigen Bereich
         *                      - max ist groeßer gleich jedem bisher betrachteten res-Eintrag
         *                      - es existiert ein res-Eintrag der max annimmt (und zwar gerade res[elect])
         *                      - elect liegt im bisher betrachteten Bereich
         */

        /*@ loop_invariant
         @      1 <= i && i <= (C+1) && (\forall int a; 1 <= a && a < i; res[a] <= max) && max == res[elect] && 1 <= elect && (elect < i || elect == 1);
         @      assignable elect, max;
         @      decreases (C - i + 1);
         @*/
        while(i <= C) {
            if(max < res[i]) {
                max = res[i];
                elect = i;
            //} else if(max == res[i]) {
            //    elect = 0;
            }
            i++;
        }
        return elect;
    }
}
