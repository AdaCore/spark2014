package Weird is

   procedure P (B : Boolean) with
     Always_Terminates => False;

   procedure Q (B : Boolean) with
     Always_Terminates => False;

   procedure R (B : Boolean) with
     Always_Terminates,
     No_Return;
   --  Terminating and No_Return is are not incompatible

end Weird;
