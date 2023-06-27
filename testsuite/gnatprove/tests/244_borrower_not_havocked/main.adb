procedure Main with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      D : Integer;
      N : List_Acc;
   end record;

   function Eq (L, R : List_Acc) return Boolean with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function Copy (L : List_Acc) return List_Acc with
     Ghost,
     Import,
     Global => null,
     Post => Eq (L, Copy'Result);

   procedure Unchanged (L : List_Acc) with
     Post => Eq (L, Copy (L)'Old);

   procedure Unchanged (L : List_Acc) is
      X : access List := L;
   begin
      null;
   end Unchanged;

   procedure Unchanged_2 (L : List_Acc) with
     Post => Eq (L, Copy (L)'Old);

   procedure Unchanged_2 (L : List_Acc) is
      X : access List := L;
   begin
      if X /= null then
         X := X.N;
      end if;
   end Unchanged_2;

   procedure Unchanged_3 (L : List_Acc) with
     Post => Eq (L, Copy (L)'Old);

   procedure Unchanged_3 (L : List_Acc) is
      X : access List := L;
   begin
      while X /= null loop
         X := X.N;
      end loop;
   end Unchanged_3;

   type Int_Acc is not null access Integer;
   type Int_Acc_Array is array (Positive range <>) of Int_Acc;

   function Eq (L, R : Int_Acc_Array) return Boolean with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function Copy (A : Int_Acc_Array) return Int_Acc_Array with
     Ghost,
     Import,
     Global => null,
     Post => Eq (A, Copy'Result);

   procedure Unchanged_4 (A : in out Int_Acc_Array) with
     Post => Eq (A, Copy (A)'Old);

   procedure Unchanged_4 (A : in out Int_Acc_Array) is
   begin
      for E of A loop
         declare
            B : access Integer := E;
         begin
            null;
         end;
      end loop;
   end Unchanged_4;

begin
   null;
end Main;
