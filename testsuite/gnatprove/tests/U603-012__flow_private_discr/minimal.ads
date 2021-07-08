package Minimal with
   SPARK_Mode
is
   procedure Dummy;

   type Complex (B : Boolean) is record
      G : Integer;
      case B is
         when True =>
            F : Integer;
         when False =>
            null;
      end case;
   end record;

   type No_F is private;
private
   type No_F is new Complex (False);
end;
