pragma Extensions_Allowed (All_Extensions);

package body Test
with SPARK_Mode
is
   type Pair is record
      Left  : Integer;
      Right : Integer;
   end record;

   Assertion_Input  : Integer := 0;
   Record_Input     : Pair := (Left => 0, Right => 0);
   Executable_Input : Integer := 0;
   Mixed_Input      : Integer := 0;

   --------------------
   -- Assertion_Only --
   --------------------

   procedure Assertion_Only is
   begin
      <<Capture>>
      null;
      pragma Assert (Assertion_Input'At (Capture) = 0);
   end Assertion_Only;

   ----------------------
   -- Record_Assertion --
   ----------------------

   procedure Record_Assertion is
   begin
      <<Capture>>
      null;
      pragma Assert (Record_Input'At (Capture).Left = 0);
   end Record_Assertion;

   ----------------
   -- Executable --
   ----------------

   procedure Executable (Output : out Integer) is
   begin
      <<Capture>>
      Output := Executable_Input'At (Capture);
   end Executable;

   -----------
   -- Mixed --
   -----------

   procedure Mixed (Output : out Integer) is
   begin
      <<Capture>>
      pragma Assert (Mixed_Input'At (Capture) = 0);
      Output := Mixed_Input'At (Capture);
   end Mixed;
end Test;
