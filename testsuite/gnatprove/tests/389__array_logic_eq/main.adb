procedure Main with SPARK_Mode is

   type Int_Array is array (Positive range <>) of Integer;

   function Eq (X, Y : Int_Array) return Boolean with
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function Eq (X, Y : Int_Array) return Boolean is
   begin
      return X'First = Y'First and X'Last = Y'Last and X = Y;
   end Eq;

   procedure Do_Nothing (X : in out Int_Array) with
     Post => Eq (X, X'Old);

   procedure Do_Nothing (X : in out Int_Array) is
      Tmp : Integer;
   begin
      if 1 in X'Range then
         Tmp := X (1);
         X (1) := 0;
         X (1) := Tmp;
      end if;
   end Do_Nothing;

   type Int_Matrix is array (Positive range <>, Positive range <>) of Integer;

   function Eq (X, Y : Int_Matrix) return Boolean with
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function Eq (X, Y : Int_Matrix) return Boolean is
   begin
      return X'First (1) = Y'First (1) and X'Last (1) = Y'Last (1) and
        X'First (2) = Y'First (2) and X'Last (2) = Y'Last (2) and X = Y;
   end Eq;

   procedure Do_Nothing (X : in out Int_Matrix) with
     Post => Eq (X, X'Old);

   procedure Do_Nothing (X : in out Int_Matrix) is
      Tmp : Integer;
   begin
      if 1 in X'Range (1) and 1 in X'Range (2) then
         Tmp := X (1, 1);
         X (1, 1) := 0;
         X (1, 1) := Tmp;
      end if;
   end Do_Nothing;
begin
   null;
end Main;
