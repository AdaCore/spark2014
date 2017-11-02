package P with SPARK_Mode, Initializes => null is
   task T;  --  task objects are always initialized in SPARK

   type R is record
      C : Integer := 0;
   end record;

   Y : R;   --  initialized by default, missing from the Initializes contract
end;
