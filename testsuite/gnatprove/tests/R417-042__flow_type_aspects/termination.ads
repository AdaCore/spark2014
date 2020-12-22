package Termination with SPARK_Mode is

   function Infinite_Loop return Boolean;

   function Rec_Func return Boolean;

   function Another_Nonterminating_Func return Boolean;

   type Int1 is new Integer with Dynamic_Predicate => Infinite_Loop;
   subtype Int2 is Int1;
   subtype Int3 is Int1 with Dynamic_Predicate => Rec_Func;

   type Int4 is new Integer;
   subtype Int5 is Int4 with Dynamic_Predicate => Infinite_Loop;

   type Int6 is private;
   type Int7 is private with Dynamic_Predicate => Another_Nonterminating_Func;

   subtype Int8 is Int7 with Dynamic_Predicate => Rec_Func;

   type Tag is tagged record
      X : Integer;
   end record
     with Dynamic_Predicate => Rec_Func and then Infinite_Loop;

   type Tag2 is new Tag with record
      Y : Integer;
   end record;

   type Tag3 is new Tag with record
      Y : Integer;
   end record
     with Dynamic_Predicate => Another_Nonterminating_Func;

   type Int_Acc is access Integer with Predicate => Rec_Func;

   type Discr_Rec (X : Natural) is private;

   function Infinite_Loop2 return Boolean;
   type Int10 is private;

private

   type Int6 is new Integer with Type_Invariant => Infinite_Loop2;

   type Int7 is new Integer
     with Type_Invariant    => Infinite_Loop2;

   type Int10 is new Int7 with Type_Invariant => True;

   type My_Arr is array (Positive range <>) of Integer;

   type Discr_Rec (X : Natural) is record
      Y : My_Arr (1 .. X) := (others => 0);
   end record
     with Type_Invariant => Infinite_Loop2;
end Termination;
