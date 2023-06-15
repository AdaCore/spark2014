package Weird is

   generic
   procedure PG (B : Boolean) with
     Always_Terminates => False;

   generic
   procedure QG (B : Boolean) with
     Always_Terminates => False;

   generic
   procedure RG (B : Boolean) with
     Always_Terminates,
     No_Return;
   --  Terminating and No_Return is are not incompatible

end Weird;
