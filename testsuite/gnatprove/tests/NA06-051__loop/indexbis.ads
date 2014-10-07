pragma SPARK_Mode;
function IndexBis (C : String; S : String) return Natural
  with Post =>
    (if IndexBis'Result = 0
       then not (for some I in S'Range => (for some J in C'Range => S (I) = C (J)))
       else
         IndexBis'Result in S'Range
     and then
       not (for some I in S'First .. IndexBis'Result - 1 => (for some J in C'Range => S (I) = C (J)))
     and then (for some J in C'Range => S (IndexBis'Result) = C (J)));
