package body A with SPARK_Mode
is

   function G (X : T) return Boolean is
      Y, Z : Boolean;
   begin
      --  SPARK has insufficient information here to determine that
      --  P does not modify the contents of X.
      --  It therefore conservatively assumes that P could modify it
      --  and treats this as an error.
      P (X      => X, --  P might modify X; regarded as illlegal in a function
         Result => Y);

      --  The following experiments deliberately
      --  violate SPARK rules:
      X.all := 3;     --  Modifying contents of X is an illegal side-effect
      Q (X      => X, --  Q does modify X; definitely illegal in a function.
         Result => Z);
      return Y and Z;
   end G;

   function G1 (X : T) return Boolean is
      Y : Boolean;
   begin
      --  SPARK can tell from the signature of R that X's contents won't
      --  be changed.
      R (X      => X,  --  Legal
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
      --  X.all := 3;  --  If uncommented, this line violates the signature
      Result := X.all = 3;
   end R;

   procedure R_Record (X      : access constant Foo;
                        Result : out Boolean) is
   begin
      Result := X.all.A = 3;
   end R_Record;

   --  Variations on P, Q and G, but using a private type.
   --  The SPARK LRM section 3.10 says
   --  "An object of an owning access type is said to be an owning object"
   --  So an object of a private type is not an owning object.
   --  Because T_Priv is a private type, the ownership rules mean
   --  Z is a constant object and assignment to the contents of the
   --  pointer is illegal.
   procedure P_Priv (Z      : in T_Priv;
                     Result : out Boolean) is
   begin
      Result := Z.all = 3;
   end P_Priv;

   procedure P1_Priv (Z      : in out T_Priv;
                      Result : out Boolean) is
   begin
      Result := Z.all = 3;
   end P1_Priv;

   --  The frontend rejects this variation on Q using a private type
   --  procedure Q_Priv (Z      : in T_Priv;
   --                    Result : out Boolean) is
   --  begin
   --     Z.all := 3;  --  Illegal as T_Priv is private
   --     Result := Z.all = 3;
   --  end Q_Priv;

   function G_Priv (X : T_Priv) return Boolean is
      Y : Boolean;
   begin
      --  SPARK "knows" that X won't be changed by P_Priv, so legal.
      P_Priv (Z      => X,
              Result => Y);
      return Y;
   end G_Priv;

   --  Variation on G1, but using a private version on type T.
   --  No warnings should be emitted.
   function G1_Priv (X : T_Priv) return Boolean is
      Y : Boolean;
   begin
      R (X      => X,  --  Legal; R doesn't modify X
         Result => Y);
      return Y;
   end G1_Priv;

   type U is not null access Boolean;

   --  Test to check that Flow correctly uses the fact that function
   --  parameters of access type are immutable.
   function Recur (X : U;
                   J : Natural) return Boolean
     with Depends => (Recur'Result => (X, J))
   is
   begin
      if J = 0 then
         return X.all;
      else
         return Recur (X, J - 1);
      end if;
   end Recur;

   --  Final dependency check
   function FP (X : U) return Boolean
     with Depends => (FP'Result => null, null => X) is
   begin
      return True;
   end;
end A;
