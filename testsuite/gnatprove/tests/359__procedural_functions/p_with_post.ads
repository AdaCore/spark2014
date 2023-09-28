package P_With_Post with SPARK_Mode is

   G : Integer := 0;

   function F1 (X : out Integer) return Integer
     with Side_Effects,
          Post => X = 0 and F1'Result = X;

   function F2 (X : in out Integer) return Integer
     with Side_Effects,
          Post => X = Integer'Min (0, X'Old) and F2'Result = X;

   function F3 (X : Integer) return Integer
     with Side_Effects,
          Global => (Output => G),
          Post => G = X and F3'Result = G;

   function F4 (X : Integer) return Integer
     with Side_Effects,
          Global => (In_Out => G),
          Post => G = Integer'Min (X, G'Old) and F4'Result = G;

   function F5 (X : Integer) return Integer
     with Side_Effects,
          Exceptional_Cases => (others => X <= 0),
          Post => X > 0 and F5'Result = X;

   function F6 (X : Integer) return Integer
     with Side_Effects,
          Exceptional_Cases => (others => False),
          Post => F6'Result = X;

   function F7 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => False,
          Post => False;

   function F8 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => True,
          Post => F8'Result = X;

   function F9 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => X > 0,
          Post => X > 0 and F9'Result = X;

   function F10 (X : Integer) return Integer
     with Side_Effects,
          Depends => (G => X, F10'Result => X),
          Post => G = X and F10'Result = X;

   function F11 (X : Integer) return Integer
     with Side_Effects,
          Depends => (G => (X, G), F11'Result => (X, G)),
          Post => G = Integer'Min (X, G'Old) and F11'Result = G;

end P_With_Post;
