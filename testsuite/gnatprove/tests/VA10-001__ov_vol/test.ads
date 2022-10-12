package Test is
   type Int is new Integer;
   A1 : aliased Int with Volatile, Alignment => 32, Async_Readers => True;
   A2 : Int := 0 with Address => A1'Address, Volatile, Alignment => 32;

   B1 : aliased Int with Volatile, Alignment => 32, Async_Writers => True;
   B2 : Int := 0 with Address => B1'Address, Volatile, Alignment => 32;

   C1 : aliased Int with Volatile, Alignment => 32, Effective_Reads => True, Async_Writers => True;
   C2 : Int := 0 with Address => C1'Address, Volatile, Alignment => 32;

   D1 : aliased Int with Volatile, Alignment => 32, Effective_Writes => True, Async_Readers => True;
   D2 : Int := 0 with Address => D1'Address, Volatile, Alignment => 32;
end Test;
