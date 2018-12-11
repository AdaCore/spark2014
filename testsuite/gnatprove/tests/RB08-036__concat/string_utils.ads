package String_Utils with SPARK_Mode is
   function Concatenate
     (A : String; B: String; C, D, E, F ,G, H, I, J, K, L : String := "")
     return String
   with
     Global => null,
     Post   => Concatenate'Result'Length = A'Length + B'Length + C'Length + D'Length + E'Length + F'Length +
                                           G'Length + H'Length + I'Length + J'Length + K'Length + L'Length;
end String_Utils;
