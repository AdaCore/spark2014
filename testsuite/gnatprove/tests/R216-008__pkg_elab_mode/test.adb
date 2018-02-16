package body Test is
   procedure Dummy is null;

   pragma Assert (False);
   --  here the SPARK_Mode is not On, so we should not get a check
end Test;
