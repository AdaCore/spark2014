procedure Flow_Crash is

   package Nested is
      type T is private with
        Default_Initial_Condition;
   private
      type T is new Integer;
   end Nested;

   type Holder is record
      F : Nested.T;
   end record;

   X : Holder := Holder'(F => <>);

begin
   null;
end;
