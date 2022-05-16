procedure Main with SPARK_Mode is

   package Private_Types is
      type OK_Rec is private;
      function "=" (X, Y : OK_Rec) return Boolean;

      type Holder is record
         X : OK_Rec;
      end record;

      C1 : constant OK_Rec;
      C2 : constant OK_Rec;
   private
      type OK_Rec is record
         G, F : Integer;
      end record;
      function "=" (X, Y : OK_Rec) return Boolean is
        (X.F = Y.F);

      C1 : constant OK_Rec := (1, 2);
      C2 : constant OK_Rec := (2, 2);
   end Private_Types;
   use Private_Types;

begin
   pragma Assert (Holder'(X => C1) /= Holder'(X => C2)); --@ASSERT:FAIL
end Main;
