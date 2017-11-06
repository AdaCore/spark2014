package Wrong_LSP with SPARK_Mode is pragma Elaborate_Body;
   type Root is tagged record
      F1 : Natural;
   end record;

   procedure Do_Nothing (R : in out Root) with
     Post'Class => R.F1 = R.F1'Old;

   type Child is new Root with record
      F2 : Natural;
   end record;

   procedure Do_Nothing (R : in out Child) with
     Post'Class => R.F2 = R.F2'Old; --@STRONGER_CLASSWIDE_POST:FAIL

end Wrong_LSP;
