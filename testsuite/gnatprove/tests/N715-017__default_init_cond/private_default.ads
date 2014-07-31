package Private_Default with SPARK_Mode is
   type Simple_Priv is private with --@DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Simple_Priv_Ok (Simple_Priv);
   type Wrong_Priv is private with --@DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Wrong_Priv_Ok (Wrong_Priv);
   type Priv_With_Glob is private with --@DEFAULT_INITIAL_CONDITION:FAIL
     Default_Initial_Condition => Priv_With_Glob_Ok (Priv_With_Glob);

   function Simple_Priv_Ok (R : Simple_Priv) return Boolean;
   function Wrong_Priv_Ok (R : Wrong_Priv) return Boolean;
   function Priv_With_Glob_Ok (R : Priv_With_Glob) return Boolean;

   procedure Set_Glob (X : Natural);

private
   pragma SPARK_Mode (Off);

   Glob : Natural := 0;

   type Simple_Priv is record
      F : Natural := 0;
   end record;
   type Wrong_Priv is record
      F : Natural := 1;
   end record;
   type Priv_With_Glob is record
      F : Natural := Glob;
   end record;

   function Simple_Priv_Ok (R : Simple_Priv) return Boolean is (R.F = 0);
   function Wrong_Priv_Ok (R : Wrong_Priv) return Boolean is (R.F = 0);
   function Priv_With_Glob_Ok (R : Priv_With_Glob) return Boolean is
     (R.F = Glob);
end;
