procedure Pred (X, Y : Positive)
  with SPARK_Mode,
       Pre => X < Y
is
   function Prop (X : Integer) return Boolean is (10 mod X /= 0)
     with Pre => X /= 0;

   type T is new Integer range X .. Y
     with Dynamic_Predicate =>
       Prop (Integer(T));  --  precondition not provable yet

   type A is array (Positive range <>) of Integer
     with Dynamic_Predicate =>
       (for all X in A'Range => Prop (X));  --  @PRECONDITION:PASS

   type R (D : Positive) is record
      case D is
         when 1 =>
            C1 : Integer;
         when 2 =>
            C2 : Float;
         when others =>
            C3 : Boolean;
      end case;
   end record
     with Dynamic_Predicate =>
       Prop (R.D) and then             --  @PRECONDITION:PASS
       (case R.D is
          when 1 => R.C1 /= 0,            --  @DISCRIMINANT_CHECK:PASS
          when 2 => R.C2 /= 0.0,          --  @DISCRIMINANT_CHECK:PASS
          when others => R.C3 /= False);  --  @DISCRIMINANT_CHECK:PASS

   --  COMMENTED OUT UNTIL O416-002 IS FIXED

   --  type R2 (D : Positive) is record
   --     C : A(1 .. D);
   --  end record
   --    with Dynamic_Predicate =>
   --      Prop (R.D) and then             --  @ PRECONDITION:PASS
   --      (for all X in R.C'Range =>
   --        Prop (X) and                  --  @ PRECONDITION:PASS
   --        Prop (R.D - X + 1));          --  @ PRECONDITION:PASS
begin
   null;
end Pred;
