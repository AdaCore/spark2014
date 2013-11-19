package Inc
  with SPARK_Mode,
       Abstract_State => (Sensor with External => Async_Writers)
is
   -- Declare a private type which will keep a trace of the
   -- values read.
   type Increasing_Indicator is private;

   -- Access (ghost) functions for the private type only intended for
   -- use in pre and post conditions or other assertion expressions
   function First (Indicator : Increasing_Indicator) return Integer
     with Convention => Ghost;

   function Second (Indicator : Increasing_Indicator) return Integer
     with Convention => Ghost;

   -- Used to check that the value returned by procedure Increases
   -- is valid (Invalid values have not been read from the Sensor).
   function Is_Valid (Indicator : Increasing_Indicator) return Boolean;

   -- Use this function to determine whether the result of the procedure
   -- Increases indicates an increasing value.
   -- It can only be called if Is_Valid (Indicator)
   function Is_Increasing (Indicator : Increasing_Indicator) return Boolean
     with Pre => Is_Valid (Indicator);

   procedure Increases (Result : out Increasing_Indicator)
     with Global => Sensor,
          Post   => (if Is_Valid (Result) then Is_Increasing (Result)=
                       (Second (Result) > First (Result)));

private
   type Increasing_Indicator is record
      Valid : Boolean;
      First, Second : Integer;
   end record;
end Inc;
