package P with SPARK_Mode is

   G : Integer := 0;

   function F1 (X : out Integer) return Integer
     with Side_Effects;

   function F2 (X : in out Integer) return Integer
     with Side_Effects;

   function F3 (X : Integer) return Integer
     with Side_Effects,
          Global => (Output => G);

   function F4 (X : Integer) return Integer
     with Side_Effects,
          Global => (In_Out => G);

   function F5 (X : Integer) return Integer
     with Side_Effects,
          Exceptional_Cases => (others => True);

   function F6 (X : Integer) return Integer
     with Side_Effects,
          Exceptional_Cases => (others => False);

   function F7 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => False;

   function F8 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => True;

   function F9 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => X > 0;

   function F10 (X : Integer) return Integer
     with Side_Effects,
          Depends => (G => X, F10'Result => X);

   function F11 (X : Integer) return Integer
     with Side_Effects,
          Depends => (G => (X, G), F11'Result => (X, G));

end P;
