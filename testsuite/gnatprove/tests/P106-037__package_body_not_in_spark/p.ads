package P with SPARK_Mode is

   function Zero return Integer is (0);

   X : Integer := 1 / Zero;

   procedure Dummy;
   --  Dummy procedure just to force body presence

end;
