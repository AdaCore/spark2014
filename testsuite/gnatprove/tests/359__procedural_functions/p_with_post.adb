package body P_With_Post with SPARK_Mode is

   procedure Error with
     No_Return,
     Always_Terminates => False,
     Exceptional_Cases => (others => False)
   is
   begin
      loop null; end loop;
   end;

   function F1 (X : out Integer) return Integer is
   begin
      X := 0;
      return X;
   end;

   function F2 (X : in out Integer) return Integer is
   begin
      X := Integer'Min (0, X);
      return X;
   end;

   function F3 (X : Integer) return Integer is
   begin
      G := X;
      return G;
   end;

   function F4 (X : Integer) return Integer is
   begin
      G := Integer'Min (X, G);
      return G;
   end;

   function F5 (X : Integer) return Integer is
   begin
      if X <= 0 then
         raise Constraint_Error;
      end if;
      return X;
   end;

   function F6 (X : Integer) return Integer is
   begin
      return X;
   end;

   function F7 (X : Integer) return Integer is
   begin
      Error;
      return X;
   end;

   function F8 (X : Integer) return Integer is
   begin
      return X;
   end;

   function F9 (X : Integer) return Integer is
   begin
      if X <= 0 then
         Error;
      end if;
      return X;
   end;

   function F10 (X : Integer) return Integer is
   begin
      G := X;
      return G;
   end;

   function F11 (X : Integer) return Integer is
   begin
      G := Integer'Min (X, G);
      return G;
   end;

   --  bodies acting as spec

   function B1 (X : out Integer) return Integer
     with Side_Effects,
          Post => X = 0 and B1'Result = X
   is
   begin
      X := 0;
      return X;
   end;

   function B2 (X : in out Integer) return Integer
     with Side_Effects,
          Post => X = Integer'Min (0, X'Old) and B2'Result = X
   is
   begin
      X := Integer'Min (0, X);
      return X;
   end;

   function B3 (X : Integer) return Integer
     with Side_Effects,
          Global => (Output => G),
          Post => G = X and B3'Result = G
   is
   begin
      G := X;
      return G;
   end;

   function B4 (X : Integer) return Integer
     with Side_Effects,
          Global => (In_Out => G),
          Post => G = Integer'Min (X, G'Old) and B4'Result = G
   is
   begin
      G := Integer'Min (X, G);
      return G;
   end;

   function B5 (X : Integer) return Integer
     with Side_Effects,
          Exceptional_Cases => (others => True),
          Post => X > 0 and B5'Result = X
   is
   begin
      if X <= 0 then
         raise Constraint_Error;
      end if;
      return X;
   end;

   function B6 (X : Integer) return Integer
     with Side_Effects,
          Exceptional_Cases => (others => False),
          Post => B6'Result = X
   is
   begin
      return X;
   end;

   function B7 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => False,
          Post => False
   is
   begin
      Error;
      return X;
   end;

   function B8 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => True,
          Post => B8'Result = X
   is
   begin
      return X;
   end;

   function B9 (X : Integer) return Integer
     with Side_Effects,
          Always_Terminates => X > 0,
          Post => X > 0 and B9'Result = X
   is
   begin
      if X <= 0 then
         Error;
      end if;
      return X;
   end;

   function B10 (X : Integer) return Integer
     with Side_Effects,
          Depends => (G => X, B10'Result => X),
          Post => G = X and B10'Result = X
   is
   begin
      G := X;
      return G;
   end;

   function B11 (X : Integer) return Integer
     with Side_Effects,
          Depends => (G => (X, G), B11'Result => (X, G)),
          Post => G = Integer'Min (X, G'Old) and B11'Result = G
   is
   begin
      G := Integer'Min (X, G);
      return G;
   end;

end P_With_Post;
