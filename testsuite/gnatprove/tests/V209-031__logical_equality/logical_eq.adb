with Ext;
procedure Logical_Eq with SPARK_Mode is
   function F (X : Integer) return Integer with Import;

   type My_Arr is array (Positive range <>) of Natural;
   function F (X : My_Arr) return Integer with Import;

   function My_Eq_1 (X, Y : My_Arr) return Boolean with
     Import,
     Annotate => (GNATprove, Logical_Equal);

   type My_Rec (L : Natural) is record
      X : Float;
      Y : My_Arr (1 .. L);
   end record;
   function F (X : My_Rec) return Integer with Import;

   function My_Eq_2 (X, Y : My_Rec) return Boolean with
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq_2 (X, Y : My_Rec) return Boolean is (X = Y) with
     SPARK_Mode => Off;
   function My_Eq_3 (X, Y : Integer) return Boolean is (Ext.My_Eq (X, Y));

   procedure Test1 (X, Y : My_Arr) with
     Global => null,
     Pre => My_Eq_1 (X, Y)
   is
   begin
      pragma Assert (X'First = Y'First);
      pragma Assert (F (X) = F (Y));
   end Test1;
   procedure Test2 (X, Y : My_Rec) with
     Global => null,
     Pre => My_Eq_2 (X, Y)
   is
   begin
      pragma Assert (F (X) = F (Y));
   end Test2;
   procedure Test3 (X, Y : Integer) with
     Global => null,
     Pre => My_Eq_3 (X, Y)
   is
   begin
      pragma Assert (F (X) = F (Y));
   end Test3;
begin
   null;
end;
