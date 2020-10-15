procedure In_Out_Pledge with SPARK_mode is
   pragma Unevaluated_Use_Of_Old (Allow);

    type List_Cell;
    type List is access List_Cell;
    type List_Cell is record
       Value : Integer;
       Next  : List;
    end record;

    function Length_Aux (L : access constant List_Cell) return Natural is
      (if L = null then 0
       elsif Length_Aux (L.Next) = Integer'Last then
            Integer'Last
       else 1 + Length_Aux (L.Next));
    pragma Annotate (GNATprove, Terminating, Length_Aux);

    function Length (L : access constant List_Cell) return Natural is (Length_Aux (L));

    function Get_Nth_Val (L : access constant List_Cell; N : Positive) return Integer is
      (if N = 1 then L.Value else Get_Nth_Val (L.Next, N - 1))
    with Pre => N <= Length (L);
    pragma Annotate (GNATprove, Terminating, Get_Nth_Val);

   type Model_Type is array (Positive range <>) of Integer with Ghost;
   function Model (X : access constant List_Cell) return Model_Type with
     Ghost,
     Post => Model'Result'First = 1 and Model'Result'Last = Length (X)
     and (for all I in 1 .. Length (X) => Model'Result (I) = Get_Nth_Val (X, I))
   is
      Res : Model_Type (1 .. Length (X)) with Relaxed_Initialization;
   begin
      for I in 1 .. Length (X) loop
         Res (I) := Get_Nth_Val (X, I);
         pragma Loop_Invariant
           (for all K in 1 .. I => Res (K)'Initialized);
         pragma Loop_Invariant
           (for all K in 1 .. I => Res (K) = Get_Nth_Val (X, K));
      end loop;
      return Res;
   end Model;

   function At_End_Borrow (T : access constant List_Cell) return access constant List_Cell is (T) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Entity => At_End_Borrow);

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
         X : access List_Cell := LL.L1;

         procedure Go_To_Next with
           Global => (In_Out => X),
           Pre  => X /= null,
           Post => Model (X) = Model (X.Next)'Old
           and At_End_Borrow (X'Old).Value = X.Value'Old
           and Integer'Min (Integer'Last - 1, Length (At_End_Borrow (X))) + 1 = Length (At_End_Borrow (X'Old))
           and Model (At_End_Borrow (X)) = Model (At_End_Borrow (X'Old).Next)
         is
         begin
            X := X.Next;
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

   end if;
end In_Out_Pledge;
