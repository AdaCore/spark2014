package test_record_cnt_ex with SPARK_Mode is
    package Hide_Id is
       function Id (X : Integer) return Integer;
    private
       pragma SPARK_Mode (Off);
       function Id (X : Integer) return Integer is (X);
    end Hide_Id;
    use Hide_Id;

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
       type F_Present is private;
       X, Y : constant No_F;
       W, Z : constant F_Present;
    private
       type No_F is new Complex (False);
       type F_Present is new Complex (True);
       X : constant No_F := (B => False, G => 5);
       Y : constant No_F := (B => False, G => Id (5));
       W : constant F_Present := (B => True, G => 5, F => 6);
       Z : constant F_Present := (B => True, G => 5, F => Id (6));
    end Nested_3;
    use all type Nested_3.No_F;
    use all type Nested_3.F_Present;

    pragma Assert (Nested_3.X = Nested_3.Y);
    pragma Assert (Nested_3.Z = Nested_3.W);
end test_record_cnt_ex;
