package Generics with SPARK_Mode is

   X : Integer := 0;
   
   generic 
      Y : Integer;
   procedure Terminating_Generic
     with Global => (In_Out => X),
     Annotate => (GNATprove, Always_Return);

   generic
      Y : Integer;
   procedure Terminating_Instance_Builder
     with Global => (In_Out => X);
   
end Generics;
