package test_record_cnt_ex with SPARK_Mode is

   type Complex (B : Boolean) is record
      G : Integer;
      case B is
         when True =>
            F : Integer;
         when False => null;
      end case;
   end record;

   package Nested_3 is
      type No_F is private;
      X : constant No_F;
   private
      type No_F is new Complex (False);
      X : constant No_F := (B => False, G => 5);
   end Nested_3;

end test_record_cnt_ex;
