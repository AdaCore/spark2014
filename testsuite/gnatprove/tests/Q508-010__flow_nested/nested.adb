package body Nested with
   Refined_State => (State_A => (A_1, A_2),
                     State_B => (B_1, B_2))
is

   A_1 : Integer;
   A_2 : Integer := 42;
   B_1 : Boolean;
   B_2 : Boolean := False;

   procedure State_A_In (X : out Boolean)
   is

      package Helper_1 with
         Abstract_State => H_1
         -- Initializes => (H_1 => (A_1, A_2))
      is
         function Check return Boolean;
      end Helper_1;

      package body Helper_1 with Refined_State => (H_1 => Cache)
      is
         Cache : constant Boolean := A_1 > A_2;
         function Check return Boolean is
         begin
            return not Cache;
         end Check;
      end Helper_1;

   begin
      X := Helper_1.Check;
   end State_A_In;

begin

   if B_2 then
      A_1 := A_2;
   else
      A_1 := 0;
   end if;

end Nested;
