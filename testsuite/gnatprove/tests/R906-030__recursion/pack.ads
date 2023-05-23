package Pack is
   subtype Small_Nat is Natural range 0 .. 100;
   subtype Small_Pos is Positive range 1 .. 100;
   type My_Arr is array (Small_Pos range <>) of Small_Nat;

   function Sum (M : My_Arr) return Natural is
     (if M'Length = 0 then 0
      else Sum (M (M'First .. M'Last - 1)) + M (M'Last))
       with Post => Sum'Result <= 100 * M'Length;
   pragma Annotate (GNATprove, Always_Return, Sum);

   procedure truncate (M : in out My_Arr; S : Natural) with
     Post => Sum (M) <= S;
end Pack;
