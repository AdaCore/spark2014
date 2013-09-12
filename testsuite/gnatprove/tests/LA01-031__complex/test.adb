procedure Test is 

   type T (D1 : Integer; D2 : Boolean) is record
      X : Integer;
      Y : Boolean;
   end record;

   type D (T1 : Boolean; T2 : Integer) is new T (D1 => T2, D2 => T1);

   type Matrix (Rows, Columns : Natural) is record
      A : String (1 .. Rows);
      B : String (1 .. Columns);
   end record;

   type Square_Matrix (Size : Natural) is new Matrix
    (Rows => Size, Columns => Size);

   generic
      type T1 (D : boolean) is private;
   package G is
      type T2 is new T1;
   end G;

   type T0 (My_Name_Is_Not_D : Boolean) is null record;

   package I is new G (T1 => T0);

begin
   null;
end Test;
