package Incomplete_Types with SPARK_Mode is
   package P1 is
      type With_Discr (X : Boolean);
      function "=" (X, Y : With_Discr) return Boolean is (True);
      type With_Discr_Ptr is access With_Discr (True);
      type With_Discr (X : Boolean) is record
         Y : With_Discr_Ptr;
      end record;
      Y : With_Discr_Ptr := new With_Discr'(X => False, others => <>);
   end P1;
   package P2 is
      type With_Discr;
      function "=" (X, Y : With_Discr) return Boolean is (True);
      type With_Discr_Ptr is access With_Discr;
      type With_Discr is array (Positive range <>) of Natural;
      subtype With_Discr_Ptr_2 is With_Discr_Ptr (1 .. 2);
   end P2;
end Incomplete_Types;
