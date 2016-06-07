package body Declare_Iterable with SPARK_Mode is

   procedure Set (X : in out Container; C : Cursor; E : Natural) is
   begin
      X.Content (C) := E;
   end Set;
end Declare_Iterable;
