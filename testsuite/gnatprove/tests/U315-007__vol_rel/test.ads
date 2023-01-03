package Test is

   X : Integer with Relaxed_Initialization;

   Y : Integer := 0 with Address => X'Address;

   A : Integer;
   B : Integer := 0 with Address => A'Address, Relaxed_Initialization;

end Test;
