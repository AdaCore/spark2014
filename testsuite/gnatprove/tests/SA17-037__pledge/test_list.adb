procedure Test_List with SPARK_Mode
is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   function At_End_Borrow (X : access constant List_Cell) return access constant List_Cell is
     (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Length (X : access constant List_Cell) return Natural is
     (if X = null then 0
      elsif Length (X.Next) = Natural'Last then Natural'Last
      else Length (X.Next) + 1)
   with Annotate => (GNATprove, Terminating);

   procedure Wrong (X : in out List) with
     Pre => Length (X) = 3
   is
      Y : access List_Cell := X;
   begin
      Y.Next := null;
      Y := Y.Next;
      for I in 1 .. 1 loop
         pragma Loop_Invariant (Length (At_End_Borrow (X)) = 1);            --  OK
         pragma Loop_Invariant (Length (At_End_Borrow (X))'Loop_Entry = 3); --  Incorrect
      end loop;
   end Wrong;

begin
   null;
end Test_List;
