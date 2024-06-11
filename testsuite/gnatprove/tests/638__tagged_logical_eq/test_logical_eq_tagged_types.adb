procedure Test_Logical_Eq_Tagged_Types with SPARK_Mode is

   type Root is tagged record
      F : Integer;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   function Eq (X, Y : Root) return Boolean with
     Pre => X in Root and Y in Root,
     Annotate => (GNATprove, Logical_Equal);

   function Eq (X, Y : Root) return Boolean is
     (X.F = Y.F);

   function Eq_Child (X, Y : Root'Class) return Boolean with
     Pre => X in Child and Y in Child,
     Annotate => (GNATprove, Logical_Equal);

   function Eq_Child (X, Y : Root'Class) return Boolean is
      C_X : constant Child'Class := Child'Class (X);
      C_Y : constant Child'Class := Child'Class (Y);
   begin
     return C_X.F = C_Y.F and C_X.G = C_Y.G;
   end Eq_Child;

begin
   null;
end Test_Logical_Eq_Tagged_Types;
