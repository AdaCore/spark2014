procedure Main with SPARK_Mode is
   package P is
      type Root (D : Boolean) is tagged private;

      type Child is new Root with private;

      function F (R : Child'Class) return Boolean;

   private
      type Root (D : Boolean) is tagged record
         case D is
            when True =>
               F : Integer := 0;
            when False =>
               null;
         end case;
      end record;

      type Child is new Root with record
         G : Integer := 0;
      end record;

      function F (R : Child'Class) return Boolean is
        (R.F = 0 and R.G = 0); --@DISCRIMINANT_CHECK:FAIL
   end P;
   use P;

begin
   null;
end Main;
