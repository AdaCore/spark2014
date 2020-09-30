package body A with SPARK_Mode
is

   function G (X : T) return Boolean is
      Y, Z : Boolean;
   begin
      --  SPARK has insufficient information here to determine that
      --  P does not modify the contents of X.
      --  It therefore conservatively assumes that P does modify it
      --  and treats this as an error.
      P (X      => X,
         Result => Y);

      --  The following experiments should (and do) all
      --  violate SPARK rules:
      X.all := 3;
      Q (X      => X,  --  Q does modify X.
         Result => Z);
      return Y and Z;
   end G;

   function G1 (X : T) return Boolean is
      Y : Boolean;
   begin
      --  SPARK can tell from the signature of R that X's contents cannot be changed.
      R (X      => X,
         Result => Y);
      return Y;
   end G1;

   procedure P (X      : in T;
                Result : out Boolean) is
   begin
      Result := X.all = 3;
   end P;

   procedure Q (X      : in T;
                Result : out Boolean) is
   begin
      --  Side-effect is legal in a procedure, even though
      --  X is an "in" parameter.
      X.all := 3;
      Result := X.all = 3;
   end Q;

   procedure R (X      : access constant Integer;
                Result : out Boolean) is
   begin
      Result := X.all = 3;
   end R;
end A;
