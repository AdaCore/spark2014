package Aggregates is

   type T is private;
   type Arr_T is private;
   type Rec_T is private;

   procedure Create_Arr (X : out Arr_T);

   procedure Update_Arr (X : in out Arr_T);

   function Get_Arr (X : Arr_T) return Integer;

   procedure Create_Rec (X : out Rec_T);

   procedure Update_Rec (X : in out Rec_T);

   function Get_Rec (X : Rec_T) return Integer;

private

   type T is new Integer with
     Type_Invariant => T /= 0;

   type Arr_T is array (1 .. 2) of T;

   type Rec_T is record
      A, B : T;
   end record;

end Aggregates;
