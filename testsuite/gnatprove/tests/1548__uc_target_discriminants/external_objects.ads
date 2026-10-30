with System;

package External_Objects with SPARK_Mode is
   type Rec (D : Integer) is record
      Value : Natural;
   end record;
   type Nat_Rec (D : Natural) is record
      Value : Natural;
   end record;
   type Items is array (1 .. 2) of Rec (0);
   type Outer is record
      Item : Rec (0);
      Data : Items;
   end record;
   type Plain is record
      Value : Natural;
   end record;

   Ordinary : Rec (0) with Import,
     Address => System'To_Address (16#1000#);
   Annotated : Rec (0) with Import, Potentially_Invalid,
     Address => System'To_Address (16#2000#);
   Nat_Annotated : Nat_Rec (0) with Import, Potentially_Invalid,
     Address => System'To_Address (16#3000#);
   Array_Annotated : Items with Import, Potentially_Invalid,
     Address => System'To_Address (16#4000#);
   Record_Annotated : Outer with Import, Potentially_Invalid,
     Address => System'To_Address (16#5000#);
   Control : Plain with Import, Potentially_Invalid,
     Address => System'To_Address (16#6000#);
end External_Objects;
