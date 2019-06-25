procedure In_Out_Pledge with SPARK_mode is
    type List_Cell;
    type List is access List_Cell;
    type List_Cell is record
       Value : Integer;
       Next  : List;
    end record;

    function Length_Aux (L : access List_Cell) return Natural is
      (if L = null then 0
       elsif Length_Aux (L.Next) = Integer'Last then
            Integer'Last
       else 1 + Length_Aux (L.Next));
    pragma Annotate (GNATprove, Terminating, Length_Aux);

    function Length (L : access List_Cell) return Natural is (Length_Aux (L));

    function Get_Nth_Val (L : access List_Cell; N : Positive) return Integer is
      (if N = 1 then L.Value else Get_Nth_Val (L.Next, N - 1))
    with Pre => N <= Length (L);
    pragma Annotate (GNATprove, Terminating, Get_Nth_Val);

   function Pledge (T : access List_Cell; B : Boolean) return Boolean is (B) with Ghost;
   pragma Annotate (GNATprove, Pledge, Entity => Pledge);

   type Two_Lists is record
      L1, L2 : List;
   end record;
   L11 : List := new List_Cell'(Value => 1, Next => null);
   L12 : List := new List_Cell'(Value => 2, Next => L11);
   L13 : List := new List_Cell'(Value => 3, Next => L12);
   LL : Two_Lists := (L1 => L13, L2 => null);

   function Rand (X : Integer) return Boolean with Import;
begin
   if Rand (1) then
      declare
         Lgth   : constant Natural := Length (LL.L1) with Ghost;
         X      : access List_Cell := LL.L1;
         I      : Natural := 0 with Ghost;
         type Model_Type is array (Positive range 1 .. Lgth) of Integer with Ghost;
         Values : Model_Type := (3, 2, 1) with Ghost;

         procedure Go_To_Next with
           Global => (In_Out => (X, I), Proof_In => (Lgth, Values, LL)),
           Pre  => Lgth < Integer'Last - 1
           and then X /= null and then Lgth - Length (X) = I
           and then Pledge (X, (if Length (X) in 0 .. Natural'Last - I then Length (LL.L1) = I + Length (X) else Length (LL.L1) = Natural'Last))
           and then Pledge (X, (for all K in 1 .. I => Get_Nth_Val (LL.L1, K) = Values (K)))
           and then Pledge (X, (for all K in I + 1 .. Length (LL.L1) => Get_Nth_Val (LL.L1, K) = Get_Nth_Val (X, K - I)))
           and then (for all K in I + 1 .. Lgth => Get_Nth_Val (X, K - I) = Values (K)),
           Post => I = I'Old + 1 and then Lgth - Length (X) = I
           and then (for all K in I + 1 .. Lgth => Get_Nth_Val (X, K - I) = Values (K))
           and then Pledge (X, (if Length (X) <= Natural'Last - I then Length (LL.L1) = I + Length (X) else Length (LL.L1) = Natural'Last))
           and then Pledge (X, (for all K in 1 .. I => Get_Nth_Val (LL.L1, K) = Values (K)))
           and then Pledge (X, (for all K in I + 1 .. Length (LL.L1) =>
                              Get_Nth_Val (LL.L1, K) = Get_Nth_Val (X, K - I)))
         is
         begin
            X := X.Next;
            I := I + 1;
         end Go_To_Next;
      begin
         pragma Assert (Get_Nth_Val (X, 1) = 3);
         pragma Assert (Get_Nth_Val (X, 2) = 2);
         pragma Assert (Get_Nth_Val (X, 3) = 1);
         if X /= null then
            Go_To_Next;
            Go_To_Next;
            X.Value := 4;
         end if;
      end;
      pragma Assert (Length (LL.L1) = 3);
      pragma Assert (LL.L1.Value = 3);
      pragma Assert (LL.L1.Next.Value = 2);
      pragma Assert (Get_Nth_Val (LL.L1, 3) = 4);
      pragma Assert (LL.L1.Next.Next.Value = 4);
   else
      declare
         Lgth   : constant Natural := Length (LL.L1) with Ghost;
         Y      : access List_Cell := LL.L1;
         X      : access List_Cell := Y;
         I      : Natural := 0 with Ghost;
         type Model_Type is array (Positive range 1 .. Lgth) of Integer with Ghost;
         Values : Model_Type := (3, 2, 1) with Ghost;

         procedure Go_To_Next with
           Global => (In_Out => (X, I), Proof_In => (Lgth, Values, Y)),
           Pre  => Lgth < Integer'Last - 1
           and then X /= null and then Lgth - Length (X) = I
           and then Pledge (X, (if Length (X) in 0 .. Natural'Last - I then Length (Y) = I + Length (X) else Length (Y) = Natural'Last))
           and then Pledge (X, (for all K in 1 .. I => Get_Nth_Val (Y, K) = Values (K)))
           and then Pledge (X, (for all K in I + 1 .. Length (Y) => Get_Nth_Val (Y, K) = Get_Nth_Val (X, K - I)))
           and then (for all K in I + 1 .. Lgth => Get_Nth_Val (X, K - I) = Values (K)),
           Post => I = I'Old + 1 and then Lgth - Length (X) = I
           and then (for all K in I + 1 .. Lgth => Get_Nth_Val (X, K - I) = Values (K))
           and then Pledge (X, (if Length (X) <= Natural'Last - I then Length (Y) = I + Length (X) else Length (Y) = Natural'Last))
           and then Pledge (X, (for all K in 1 .. I => Get_Nth_Val (Y, K) = Values (K)))
           and then Pledge (X, (for all K in I + 1 .. Length (Y) =>
                              Get_Nth_Val (Y, K) = Get_Nth_Val (X, K - I)))
         is
         begin
            X := X.Next;
            I := I + 1;
         end Go_To_Next;
      begin
         pragma Assert (Get_Nth_Val (X, 1) = 3);
         pragma Assert (Get_Nth_Val (X, 2) = 2);
         pragma Assert (Get_Nth_Val (X, 3) = 1);
         if X /= null then
            Go_To_Next;
            Go_To_Next;
            X.Value := 4;
         end if;
      end;
      pragma Assert (Length (LL.L1) = 3);
      pragma Assert (LL.L1.Value = 3);
      pragma Assert (LL.L1.Next.Value = 2);
      pragma Assert (LL.L1.Next.Next.Value = 4);
   end if;
end In_Out_Pledge;
