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
         Abstract_State => H_1,
         Initializes => (H_1 => (A_1, A_2))
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

   procedure State_A_In_Out
   is

      package Helper_2 with Abstract_State => H_2
      is
         procedure Set (X : Integer);
         function Get return Integer;
      end Helper_2;

      package body Helper_2 with Refined_State => (H_2 => Tmp)
      is
         Tmp : Integer;
         procedure Set (X : Integer) is
         begin
            Tmp := X;
         end Set;
         function Get return Integer is (Tmp);
      end Helper_2;

   begin
      Helper_2.Set (A_1);
      A_1 := A_2;
      A_2 := Helper_2.Get;
   end State_A_In_Out;

   procedure State_A_Out
   is
      package Helper_3 with Abstract_State => H_3
      is
         procedure P2;
         procedure P3;
         procedure Get (X, Y : out Integer);
      end Helper_3;

      procedure P1;

      package body Helper_3 with Refined_State => (H_3 => (H_3_A, H_3_B))
      is
         H_3_A : Integer;
         H_3_B : Integer;

         procedure P2 is
         begin
            H_3_A := 0;
            P1;
         end P2;

         procedure P3 is
         begin
            H_3_B := 0;
         end P3;

         procedure Get (X, Y : out Integer)
         is
         begin
            X := H_3_A;
            Y := H_3_B;
         end Get;
      end Helper_3;

      procedure P1 is
      begin
         Helper_3.P3;
      end P1;

   begin
      Helper_3.P2;
      Helper_3.Get (A_1, A_2);
   end State_A_Out;

begin

   if B_2 then
      A_1 := A_2;
   else
      A_1 := 0;
   end if;

end Nested;
