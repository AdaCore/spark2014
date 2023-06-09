procedure Main with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      D : Integer;
      N : List_Acc;
   end record;

   function At_End (X : access constant List) return access constant List is
     (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Eq (L, R : access constant List) return Boolean with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function Next (X : not null access List) return access List with
     Post => X.D = At_End (X).D
     and then Eq (At_End (X).N, At_End (Next'Result));

   function Next (X : not null access List) return access List is
   begin
      return X.N;
   end Next;

   L : List_Acc := new List'(1, new List'(2, new List'(3, new List'(4, new List'(5, null)))));
begin
   declare
      B : access List := Next (Next (L));
   begin
      B.D := 42;
   end;

   pragma Assert (L.D = 1);
   pragma Assert (L.N.D = 2);
   pragma Assert (L.N.N.D = 42);
   pragma Assert (L.N.N.N.D = 4);
   pragma Assert (L.N.N.N.N.D = 5);
   pragma Assert (L.N.N.N.N.N = null);
end Main;
