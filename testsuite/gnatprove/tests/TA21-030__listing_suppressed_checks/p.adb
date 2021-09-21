package body P
  with SPARK_Mode => On
is
   package Inner is
      procedure Do_Nothing (S : in Integer; R : out Integer)
        with Depends => (R => S);
   end Inner;

   package body Inner is separate; --  SPARK_Mode => Off

   subtype Neg_Ints is Integer range Integer'First .. -1;

   function Add_Or_Subtract (I : Integer) return Integer is
   begin
       if I < Natural'Last then
           return I + 1;
       elsif I > Natural'First then
           return I - 1;
       else
           return I;
       end if;
   end Add_Or_Subtract;

   function Assume_Natural (X : Integer) return Integer is
   begin
      pragma Assume (X in Natural);
      --  This `pragma Assume (X not in Neg_Ints);` is redundant, but we want
      --  this counted in gnatprove.out anyway, because all pragma Assumes are
      --  potentially dangerous!
      pragma Assume (X not in Neg_Ints);
      pragma Assert (X >= 0);
      return Add_Or_Subtract (X);
   end Assume_Natural;

   procedure Annotate_Intentional (C : Boolean) is
      X : Integer;
      Z : Integer;
   begin
      if C then
         X := 1;
      end if;
      if X < 0 then
         Inner.Do_Nothing (Z, X);
      end if;
      pragma Annotate (Gnatprove, Intentional,"""X"" might not be initialized","");
      pragma Annotate (Gnatprove, Intentional,"""Z"" is not initialized","");
   end Annotate_Intentional;
end P;
