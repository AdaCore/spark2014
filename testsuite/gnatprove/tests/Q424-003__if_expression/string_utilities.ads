package String_Utilities with SPARK_Mode is

  function Head (S : String) return Character is (S (S'First));
  function Tail (S : String) return String is (S (S'First +1 .. S'Last));

  function Is_Subsequence (Subseq, Seq : String) return Boolean is
    (if Subseq = "" then True
     elsif Seq = "" then False
     elsif Head (Subseq) = Head (Seq)
     then Is_Subsequence (Tail (Subseq), Tail (Seq))
     else Is_Subsequence (Subseq, Tail (Seq)));

  function Slow_LCS_Length (S1, S2 : String) return Natural
  is
    (if S1 = "" or S2 = "" then 0
     elsif Head (S1) = Head (S2)
       then 1 + Slow_LCS_Length (Tail (S1), Tail (S2))
    else
       Integer'Max (Slow_LCS_Length (S1, Tail (S2)),
                    Slow_LCS_Length (Tail (S1), S2)));

  function Longest_Common_Subsequence (S1, S2 : String) return String with
  Post =>
    (Is_Subsequence (Longest_Common_Subsequence'Result, S1) and
     Is_Subsequence (Longest_Common_Subsequence'Result, S2) and
     Longest_Common_Subsequence'Result'Length = Slow_LCS_Length (S1, S2));

end String_Utilities;
