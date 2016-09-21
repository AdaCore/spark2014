package body BV_Arrays with SPARK_Mode is

   function Create (C : Mod_16) return My_Array is
      A : My_Array (0 .. C) := (others => 0);
   begin
      return A;
   end Create;
end BV_Arrays;
