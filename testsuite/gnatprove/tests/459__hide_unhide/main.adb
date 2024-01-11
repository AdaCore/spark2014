procedure Main with SPARK_Mode is

   package Visible_By_Default is

      function My_And (X, Y : Boolean) return Boolean is (X and Y);

   end Visible_By_Default;

   package body Visible_By_Default is

      function Use_And (X, Y : Boolean) return Boolean is
      begin
         return My_And (X, Y);
      end Use_And;
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", My_And);

      function Call_Use_And (X, Y : Boolean) return Boolean with
        Post => Call_Use_And'Result = (X and Y) -- @POSTCONDITION:FAIL
      is
      begin
         return Use_And (X, Y);
      end Call_Use_And;

      function Use_And_2 (X, Y : Boolean) return Boolean;
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", My_And);

      function Use_And_2 (X, Y : Boolean) return Boolean is
      begin
         return My_And (X, Y);
      end Use_And_2;

      function Call_Use_And_2 (X, Y : Boolean) return Boolean with
        Post => Call_Use_And_2'Result = (X and Y) -- @POSTCONDITION:FAIL
      is
      begin
         return Use_And_2 (X, Y);
      end Call_Use_And_2;

      function Use_And_3 (X, Y : Boolean) return Boolean is
         pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", My_And);
      begin
         return My_And (X, Y);
      end Use_And_3;

      function Call_Use_And_3 (X, Y : Boolean) return Boolean with
        Post => Call_Use_And_3'Result = (X and Y) -- @POSTCONDITION:FAIL
      is
      begin
         return Use_And_3 (X, Y);
      end Call_Use_And_3;

   end Visible_By_Default;

begin
   null;
end Main;
