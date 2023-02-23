package body Use_Simple_Private_Type with SPARK_Mode is
   function Add (X, Y : T) return T is
   begin
      if Is_Zero (X) then
         return Y;
      end if;
      return N (Add (P (X), Y));
      pragma Annotate (GNATprove,
                    False_Positive,
                    "terminating annotation on ""Add"" could be incorrect",
                    "function P is missing a postcondition to prove " &
                    "termination of Add and Mul");
   end Add;

   procedure Add (X : in out U; Y : U) is
   begin
      if Is_Zero (Y) then
         return;
      end if;
      X := N (X);
      Add (X, P (Y));
   end Add;

   function Mul (X, Y : T) return T is
   begin
      if Is_Zero (X) then
         return T (O);
      end if;
      return Add (Y, Mul (P (X), Y));
      pragma Annotate (GNATprove,
                       False_Positive,
                       "terminating annotation on ""Mul"" could be incorrect",
                       "function P is missing a postcondition to prove " &
                       "termination of Add and Mul");
   end Mul;

   procedure Mul (X : in out U; Y : U) is
      X_I : constant U := X;
   begin
      if Is_Zero (Y) then
         X := U (O);
         return;
      end if;
      Mul (X, P (Y));
      Add (X, X_I);
   end Mul;
end Use_Simple_Private_Type;
