pragma Extensions_Allowed (All_Extensions);

package body Test
with SPARK_Mode
is
   type Index is range 1 .. 2;
   type Value_Array is array (Index) of Integer;

   Values       : Value_Array := (others => 0);
   Direct_Value : Index := 1;
   Direct_Check : Integer := 0;
   Global_Value : Index := 1;

   -----------------
   -- Direct_Call --
   -----------------

   procedure Direct_Call is
      function Pick (Value : Index; Checked : Integer) return Index with
        Depends => (Pick'Result => Value, null => Checked);

      function Pick (Value : Index; Checked : Integer) return Index is (Value);
   begin
      <<Capture>>
      null;
      pragma
        Assert
          (Values (Pick (Direct_Value, Direct_Check))'At (Capture) = 0);
   end Direct_Call;

   -----------------
   -- Global_Call --
   -----------------

   procedure Global_Call is
      function Read return Index with
        Global  => (Input => Global_Value),
        Depends => (Read'Result => Global_Value);

      function Read return Index is (Global_Value);
   begin
      <<Capture>>
      null;
      pragma Assert (Values (Read)'At (Capture) = 0);
   end Global_Call;
end Test;
