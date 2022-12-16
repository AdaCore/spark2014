procedure PointArr with SPARK_Mode is

   type T is array (Integer range <>) of Integer;

   type T_Ptr is access T;

   procedure P (X : T_Ptr; I, V : Integer)
     with Pre => X /= null and then I in X'Range,
     Post => X (I) = V;

   procedure P (X : T_Ptr; I, V : Integer) is
   begin
      X (I) := V;
   end P;

   type R (D : Natural) is record
      C : T (1 .. D);
   end record;

   type R_Ptr is access R;

   procedure P (X : R_Ptr; I, V : Integer)
     with Pre => X /= null and then I in X.C'Range,
     Post => X.C (I) = V;

   procedure P (X : R_Ptr; I, V : Integer) is
   begin
      X.C (I) := V;
   end P;

   Arr : T_Ptr := new T'(1 .. 10 => 0);
   Rec : R_Ptr := new R'(D => 10, C => (1 .. 10 => 0));
begin
   pragma Assert (Arr'First = 1);
   P (Arr, 1, 1);
   pragma Assert (Arr (1) = 1);
   pragma Assert (Arr'First = 1);
   pragma Assert (Rec.D = 10);
   P (Rec, 1, 1);
   pragma Assert (Rec.C (1) = 1);
   pragma Assert (Rec.D = 10);
end PointArr;
