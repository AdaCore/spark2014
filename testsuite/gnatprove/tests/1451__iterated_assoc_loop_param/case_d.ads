package Case_D with SPARK_Mode is
   subtype Cnt is Natural range 1 .. 8;
   type Outp is array (Cnt) of Natural;
   function Build (C : Cnt) return Outp is
     ((for I in Cnt range 1 .. C => I));
end Case_D;
